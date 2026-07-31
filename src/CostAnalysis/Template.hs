{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module CostAnalysis.Template where

import Prelude hiding (sum, or, and)

import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Lens.Micro.Platform
import Data.Maybe (fromMaybe)
import Data.Bifunctor (first)

import Primitive(Id, freeVars, Substitutable(..), substVar, toIntegerExact, dbg)
import CostAnalysis.Coeff
import Control.Monad.State
import qualified CostAnalysis.Constraint as C
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size
import Syntax.Measure
import CostAnalysis.Constraint hiding (ConstTerm, VarTerm)

--------------------------------------------------------------------------------
-- General Templates
--------------------------------------------------------------------------------

class (Show a) => Template a where
  infixl 9 !
  (!) :: a -> ResourceTerm -> ArithExpr
  infixl 9 !?
  (!?) :: a -> ResourceTerm -> ArithExpr
  terms :: a -> Set ResourceTerm
  args :: a -> [Id]
  empty :: a -> Bool
  merge :: a -> a -> a
  amortisedCost :: a -> a

costTerms :: Set ResourceTerm -> Set ResourceTerm
costTerms = S.filter (not . isPotential) 
  where isPotential (RTPhi _) = True
        isPotential _ = False

--------------------------------------------------------------------------------
-- FreeTemplate
--------------------------------------------------------------------------------

data FreeTemplate = FreeTemplate {
  _ftId :: Int,
  _ftTerms :: Set ResourceTerm
} deriving (Eq, Show)

makeLenses ''FreeTemplate

emptyTempl :: Int -> [Id] -> FreeTemplate
emptyTempl id args = FreeTemplate {
  _ftId=id,
  _ftTerms=S.empty}

instance Template FreeTemplate where
  terms q = q^.ftTerms
  empty = S.null . _ftTerms
  args q = S.toList $ freeVars (q^.ftTerms)
  (!) templ term = case coeffForTerm templ term of
    Just q -> CoeffTerm q
    Nothing -> error $ "Invalid index '" ++ show term ++ "' for template '" ++ show templ ++ "'."
  (!?) templ term = case coeffForTerm templ term of
    Just q -> CoeffTerm q
    Nothing -> C.ConstTerm 0
  merge q p = FreeTemplate {
    _ftId = q^.ftId,
    _ftTerms = (q^.ftTerms) `S.union` (p^.ftTerms)}
  amortisedCost q = q & ftTerms %~ costTerms

instance Substitutable FreeTemplate where
  subst env t = t & ftTerms %~ S.map (subst env)

coeffForTerm :: FreeTemplate -> ResourceTerm -> Maybe Coeff
coeffForTerm templ term =
  if S.member term (templ^.ftTerms) then
    Just $ Coeff (templ^.ftId) term 
  else Nothing

coeffForTemplate :: FreeTemplate -> ResourceTerm -> Coeff
coeffForTemplate templ = Coeff (templ^.ftId)

instance HasCoeffs FreeTemplate where
  getCoeffs templ = map (coeffForTemplate templ) $ S.toList (templ^.ftTerms)

defineFrom :: Int -> FreeTemplate -> FreeTemplate
defineFrom id templ = templ { _ftId=id }

--------------------------------------------------------------------------------
-- Free Signatures
--------------------------------------------------------------------------------

data FreeSig = FreeSig {
  _fsFrom :: FreeTemplate
  , _fsTo :: FreeTemplate
  , _fsBinder :: Id
  , _fsFormArgs :: [Id]
  } deriving Show

makeLenses ''FreeSig

--------------------------------------------------------------------------------
-- BoundTemplate
--------------------------------------------------------------------------------

newtype BoundTemplate = BoundTemplate {
  btCoeffs :: Map ResourceTerm Rational}
  deriving (Eq, Show)

instance Template BoundTemplate where
  args = S.toList . freeVars . M.keys . btCoeffs
  terms t = M.keysSet (btCoeffs t)
  empty t = M.null (btCoeffs t)
  (!) t term = C.ConstTerm $ btCoeffs t M.! term
  (!?) t term = C.ConstTerm $ fromMaybe 0 (btCoeffs t M.!? term)
  merge q p = BoundTemplate {
    btCoeffs = btCoeffs q `M.union` btCoeffs p}
  amortisedCost q = let keys' = costTerms (M.keysSet (btCoeffs q)) in
    BoundTemplate (M.restrictKeys (btCoeffs q) keys')
  

bindTemplate :: FreeTemplate -> Map Coeff Rational -> BoundTemplate
bindTemplate q values = BoundTemplate
  (M.fromList [(i, v)
              | c@(Coeff _ i) <- getCoeffs q,
                let v = fromMaybe 0 (values M.!? c)])

sizeTransformFromTempl :: [Id] -> BoundTemplate -> SizeTransform
sizeTransformFromTempl args templ = let rhs = foldr go emptySizeSum $ M.toList (btCoeffs templ) in
  SizeTransform args rhs
  where go :: (ResourceTerm, Rational) -> SizeSum -> SizeSum
        go (RTSize x, k) = addSizeTerm (VarTerm x (fromRat k)) 
        go (RTId, k) = addSizeTerm (ConstTerm (fromRat k)) 
        go _ = \_ -> error $ "given template contains non size term: " ++ show templ
        
        fromRat k = case toIntegerExact k of
          Just n -> fromIntegral n
          Nothing -> error "encountered rational coeffient in size transform."

--------------------------------------------------------------------------------
-- TermTemplate
--------------------------------------------------------------------------------

newtype ArithTemplate = ArithTemplate {
  ttTerms :: Map ResourceTerm ArithExpr}  
  deriving(Show)

instance Template ArithTemplate where
  terms templ =  M.keysSet $ ttTerms templ
  args = S.toList . freeVars . M.keys . ttTerms 
  empty = M.null . ttTerms
  (!) templ term = ttTerms templ M.! term
  (!?) templ term = fromMaybe (C.ConstTerm 0) $ ttTerms templ M.!? term
  merge q p = ArithTemplate {
    ttTerms = ttTerms q `M.union` ttTerms p}


zeroTemplate = ArithTemplate M.empty


--------------------------------------------------------------------------------
-- Measure Templates
--------------------------------------------------------------------------------

type instance  Carrier 'TemplPotential = FreeTemplate

data EnrichedMeasureEnv = EnrichedMeasureEnv {
  emSizeMeasure :: MeasureAlgebra Size, 
  emPotentialMeasure :: Either (MeasureAlgebra Potential) (MeasureAlgebra TemplPotential)
} deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Template Equality
--------------------------------------------------------------------------------

data SubstValue =
  ExpandCtor ConstPat EnrichedMeasureEnv
  | TransformApp [Id] SizeTransform
  deriving Show

-- | Assert that the template 'q' subject to a substitution 'subst', equals template 'p' after normalization. 
--
-- Formula: q[x -> v] -^-> q' = p
--
assertEqSubst :: Bool -> (Id, SubstValue) -> FreeTemplate -> FreeTemplate -> (Set ResourceTerm, [Formula])
assertEqSubst checkTarget subst q p = (rhsTerms, constrain reducts)
  where constrain rs = [ Eq
                         (if checkTarget 
                          then p!?tgt
                          else CoeffTerm (Coeff (p^.ftId) tgt))
                         (sum (map termFromSrc srcs))
                       | (tgt, srcs) <- rs, (not . isZero) tgt] 
        termFromSrc (1, t) = q!t
        termFromSrc (k, t) = prod2 (C.ConstTerm k) (q!t)
        rhsTerms = S.fromList $ map fst reducts
        reducts = mergeTerms
                  . reduceTerms subst $ S.toList (terms q)

-- dont forget that the flips the templates
mergeTerms :: [(ResourceTerm, ResourceTerm)] -> [(ResourceTerm, [(Rational, ResourceTerm)])]
mergeTerms xs = M.toList
  $ M.fromListWith (++) [origin (src, tgt) | (src, tgt) <- xs]
  where origin (src, RTScale k tgt) = (tgt, [(k, src)])
        origin (src, tgt) = (tgt, [(1, src)])

reduceTerms :: (Id, SubstValue) -> [ResourceTerm] -> [(ResourceTerm, ResourceTerm)]
reduceTerms subst = concatMap go
  where 
    go t = [(t, t') | t' <- concatMap normTerm (reduceTerm subst t)]

reduceTerm :: (Id, SubstValue) -> ResourceTerm -> [ResourceTerm]
reduceTerm subst (RTSize x) = let sizes = reduceSizeSum subst (sizeVar x) in
  RTScale (fromIntegral $ _ssConstant sizes) RTId :
  [if k > 1
   then RTScale (toRational k) (RTSize x)
   else RTSize x
  | (x, k) <- M.toList (_ssCoeffs sizes) ]
reduceTerm subst (RTLog ss) = [RTLog $ reduceSizeSum subst ss]
reduceTerm (x,  ExpandCtor pat mEnv) t@(RTPhi y)
  | x == y = case emPotentialMeasure mEnv of
      Left potAlg -> apply potAlg pat
      Right _ -> error "not implemented"
  | otherwise = [t]
reduceTerm (x,  _) t@(RTPhi _) = [t]
reduceTerm subst t@(RTBinoms ss)
  = [RTBinoms $ map (first (reduceSizeSum subst)) ss]
reduceTerm _ RTId = [RTId]
reduceTerm subst t = error $ "subst: " ++ show subst ++ ", term: " ++ show t


reduceSizeSum :: (Id, SubstValue) -> SizeSum -> SizeSum
reduceSizeSum (x, ExpandCtor pat mEnv) sum =
  let sizeAlg = emSizeMeasure mEnv in
    sizeSubst (x, apply sizeAlg pat) sum
reduceSizeSum (x, TransformApp args st) sum =
  sizeSubst (x, applyST st args) sum


normTerm :: ResourceTerm -> [ResourceTerm]
normTerm (RTLog s) | M.null (s^.ssCoeffs) &&
                     s^.ssConstant == 2 = [RTId]
normTerm (RTBinoms []) = [RTId]
normTerm (RTBinoms bs) = foldr (distributeBinoms . normBinom) [] bs
normTerm t = [t]

distributeBinoms :: [ResourceTerm] -> [ResourceTerm] -> [ResourceTerm]
distributeBinoms as [] = as
distributeBinoms [] bs = bs
distributeBinoms as bs = [multBinoms a b | a <- as, b <- bs]

multBinoms :: ResourceTerm -> ResourceTerm -> ResourceTerm
multBinoms (RTBinoms as) (RTBinoms bs) = RTBinoms $ as ++ bs

normBinom :: (SizeSum, Int) -> [ResourceTerm]
normBinom (SizeSum coeffs 1, k) = case M.keys coeffs of
  [x] -> RTBinoms [(sizeVar x, k)] :
    [RTBinoms [(sizeVar x, k - 1)] | k - 1 >= 0]
normBinom (SizeSum coeffs 0, k) = case M.keys coeffs of
  [x, y]   -> [RTBinoms [(sizeVar x, r),
                         (sizeVar y, k - r)] | r <- [0..k]]

--------------------------------------------------------------------------------
-- Template Operations
--------------------------------------------------------------------------------



-- scale :: (Template a) => a -> ArithExpr -> ArithTemplate
-- scale q k = ArithTemplate $
--   M.fromList [(idx, C.prod2 (q!idx) k) | idx <- S.toList (terms q)]


add :: (Template a, Template b) => a -> b -> ArithTemplate
add q p = ArithTemplate $ M.fromList
  [(idx, C.sum [q!?idx, p!?idx])
  | idx <- S.toList $ terms q `S.union` terms p]

-- sub :: (Template a, Template b) => a -> b -> TermTemplate
-- sub q p = TermTemplate (args q `L.union` args p) (ghosts q `L.union` ghosts p)$
--              M.fromList [(idx, C.sub [q!?idx, p!?idx])
--                         | idx <- S.toList $ terms q `S.union` terms p]

-- sum :: (Template a) => a -> Term
-- sum q = C.sum [q!i | i <- S.toList $ terms q]


assertEq :: (Template a, Template b) => a -> b -> [Formula]
assertEq q p = concat [C.eq (q!?idx) (p!?idx) | idx <- S.toList $ terms q `S.union` terms p]

assertEqExceptTerm :: (Template a, Template b) => ResourceTerm -> (ArithExpr -> ArithExpr) -> a -> b -> [Formula]
assertEqExceptTerm t f q p = concat $
  C.eq (q!?t) (f (p!?t)) :
  [C.eq (q!?idx) (p!?idx)
  | idx <- S.toList $ terms q `S.union` terms p,
    idx /= t]



-- | Asserts that template 'q' with variable 'x' substituted for 'y' 
-- is equivalent to template 'p'.
--
-- Formula: q[x -> y] = p
--
assertEqVarSubst :: (Template a, Template b) => Id -> Id -> a -> b -> [Formula]
assertEqVarSubst x y q p = concat [(q!?t) `eq` (p!?substVar x y t) | t <- S.toList $
                                    terms q
                                    `S.union`
                                    (terms p S.\\ substVar x y (terms q))]

-- | Asserts that template 'q' with multiple variables substituted 
-- is equivalent to template 'p'.
--
-- Formula: q[xs -> ys] = p
--
assertEqVarsSubst :: (Template a, Template b) => [Id] -> [Id] -> a -> b -> [Formula]
assertEqVarsSubst xs ys q p = 
  concat [(q !? t) `eq` (p !? substMultiple t) | t <- S.toList $
           terms q
           `S.union`
           (terms p S.\\ S.map substMultiple (terms q))]
  where
    -- Pair up the source and target variables
    substs = zip xs ys
    -- Apply each substitution sequentially to the term
    substMultiple qt = foldl (\accTerm (x, y) -> substVar x y accTerm) qt substs


-- assertLe :: (Template a, Template b) => a -> b -> [Formula]
-- assertLe q p = concat [C.le (q!?idx) (p!?idx) | idx <- S.toList $ terms q `S.union` terms p]

-- assertGe :: (Template a, Template b) => a -> b -> [Formula]
-- assertGe q p = concat [C.ge (q!?idx) (p!?idx) | idx <- S.toList $ terms q `S.union` terms p]

-- assertGeZero :: Template a => a -> [Formula]
-- assertGeZero = (`assertGe` zeroTemplate)

-- assertZero :: Template a => a -> [Formula]
-- assertZero = (`assertEq` zeroTemplate)

-- assertZeroExcept :: Template a => a -> Set ResourceTerm -> [Formula]
-- assertZeroExcept q except = concat [ if idx `S.member` except
--                                      then C.eq (q!idx) (ConstTerm 1)
--                                      else C.zero (q!idx)
--                                    | idx <- S.toList $ terms q]

-- unifyAssertEq :: (Template a, Template b) => a -> b -> [Formula]
-- unifyAssertEq q p = concat [C.eq (q!?idx) p'
--                           | idx <- S.toList $ terms q,
--                             let p' | justConst idx = p!?idx 
--                                    | length argsQ == length argsP
--                                   = p!?substitute argsQ argsP idx
--                                    | otherwise = ConstTerm 0]
--   where argsP = if L.null $ args p `L.intersect` ghosts p then ghosts p ++ args p else args p
--         argsQ = if length (args q) < length argsP
--                 then ghosts p ++ args q
--                 else args q

                  
-- unifyAssertEqBy :: (Template a, Template b) => a -> b -> [Id] -> [Formula]
-- unifyAssertEqBy q p qArgs = let pArgs = (ghosts p ++ args p) 
--                                 qArgs' = if length qArgs < length pArgs
--                                          then ghosts p ++ qArgs
--                                          else qArgs in
--                                   concat [C.eq (q!?idx) (p!?substitute qArgs' pArgs idx)
--                                  | idx <- S.toList $ terms q]

-- | @'apply'@ returns a mapping between template indicies, that allow to apply function represented by
--   represented by the second template to be applied to the argument of the first template.
-- 
-- For two potentials \(\Phi(V), \Psi(W)\), this enables to obtain \(\Psi(V)\), a potential
-- with the arguments of \(\Phi\), applied to \(\Psi\), which can be used to calculate
-- the amortized costs by subtracting \(\Phi(V) - \Psi(V)\). Typically we want this potential
-- to be expressed in terms of the original coefficients of \(\Phi\), which can be accomplished by
-- appyling the unfier to lookup the coefficients.
--
-- If the potentials have an equal number of arguments unification just maps the arguments by
-- their position.
-- In the case where \(|V| > |W|\), we rely on a definition from Sleator and Tarjan, where we
-- define the potential of collection of arguments as the sum of the individual potentials.
--
-- \[\Psi(x_1, \dots, x_n) = \Psi(x_1) + \dots + \Psi(x_n)\]
--
-- This allows us to apply a potential \(\Psi(x) \), defined for only one argument to multible
-- arguments.
--
-- __Example:__ When calculating the costs of the meld operation that merges to two heaps, the
-- potentials differ in the number of their arguements. 
--
-- \[\Phi(x,y) = \mathcal{A}_{\mathbb{merge}} + \Psi(x) + \Psi(y), \Psi(z) = \Psi(z)\]
-- after unificication we get
-- \[\Psi(x,y) = \Psi(x) + \Psi(y)\]
-- so
-- \[\Phi(x,y) - \Psi(x,y) = \mathcal{A}_{\mathbb{merge}}\]
-- apply :: (Template a, Template b) => a -> b -> Map ResourceTerm ResourceTerm
-- apply q p | length (args q) == length (args p) =
--             let s = M.fromList (zip (args q) (args p)) in
--               M.fromList [(i, substitute (args q) (args p) i) | i <- S.toList (terms q)]
-- apply q p = case args p of
--               [] -> M.empty
--               [y] -> M.fromList [(i, substitute (args q)
--                                    (replicate (length (args q)) y) i)
--                                 | i <- S.toList (terms q),
--                                   isPure i || justConst i || singleVar i]
--               _ys_greater_xs -> error $ "cannot apply potential function " ++ show p ++ " to arguments " ++ show (args q)

-- symbolicCost :: (Template a, Template b) => a -> b -> TermTemplate
-- symbolicCost q p = TermTemplate (args q) (ghosts q) $  
--   M.fromList [(idx, C.sub [q!idx, tP]) 
--              | idx <- S.toList $ terms q,
--                let tP = maybe (ConstTerm 0) (p!?) (u M.!? idx)] 
--   where u = apply q p

-- calculateBound :: ((FreeTemplate, FreeTemplate), FreeTemplate) -> Map Coeff Rational -> BoundTemplate
-- calculateBound ((from, fromRef), to) solution =
--   let diff = BoundTemplate (args from) (ghosts from) $ M.fromList
--         [(idx, from' M.! idx - fromMaybe 0 ((to' M.!?) =<< (u M.!? idx)))
--         | idx <- S.toList $ terms from] in
--     addValues diff qe
--   where q@(BoundTemplate _ from') = bindTemplate from solution
--         qe = bindTemplate fromRef solution
--         p@(BoundTemplate _ to') = bindTemplate to solution
--         u = apply q p





