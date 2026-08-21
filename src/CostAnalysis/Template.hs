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

import Primitive(Id, freeVars, Substitutable(..), substVar, toIntegerExact)
import CostAnalysis.Coeff
import qualified CostAnalysis.Constraint as C
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size
import Syntax.Measure hiding (Eq)
import CostAnalysis.Constraint hiding (ConstTerm, VarTerm)
import qualified Data.Text as T
import qualified Data.MultiSet as MSet

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

sizeTransformFromTempl :: [Id] -> BoundTemplate -> Relation -> SizeTransform
sizeTransformFromTempl args templ rel = let rhs = foldr go emptySizeSum $ M.toList (btCoeffs templ) in
  SizeTransform args rhs rel
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
-- Measure Enviroment
--------------------------------------------------------------------------------

data EnrichedMeasureEnv = EnrichedMeasureEnv {
  emSizeMeasure :: MeasureAlgebra Size, 
  emPotentialMeasure :: Maybe (MeasureAlgebra Potential)
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
        termFromSrc (C.ConstTerm 1, t) = q!t
        termFromSrc (k, t) = prod2 k (q!t)
        rhsTerms = S.fromList $ map fst reducts
        reducts = mergeTerms
                  . reduceTerms subst $ S.toList (terms q)

-- dont forget that the flips the templates
mergeTerms :: [(ResourceTerm, ResourceTerm)] -> [(ResourceTerm, [(ArithExpr, ResourceTerm)])]
mergeTerms xs = M.toList
  $ M.fromListWith (++) [origin (src, tgt) | (src, tgt) <- xs]
  where origin (src, RTScale k tgt) = (tgt, [(C.ConstTerm k, src)])
        origin (src, RTCoeffScale i idx tgt) = (tgt, [(CoeffTerm (Coeff i idx), src)])
        origin (src, tgt) = (tgt, [(C.ConstTerm 1, src)])

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
reduceTerm subst (RTBinom ss k) = [RTBinom (reduceSizeSum subst ss) k]
reduceTerm (x,  ExpandCtor pat mEnv) t@(RTPhi y)
  | x == y = case emPotentialMeasure mEnv of
      Just potAlg -> apply potAlg pat
      Nothing -> error $ "missing potential measure for " ++ T.unpack x
  | otherwise = [t]
reduceTerm (x,  _) t@(RTPhi _) = [t]
reduceTerm subst (RTProd ts) = [RTProd $ MSet.fromList $ concatMap (reduceTerm subst) ts]
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
normTerm (RTProd ts) | all isOne ts = [RTId]
                     | otherwise    = foldr (distribute . normTerm) [RTId] ts
normTerm (RTBinom ss k) = normBinom ss k
normTerm t = [t]

distribute :: [ResourceTerm] -> [ResourceTerm] -> [ResourceTerm]
distribute as [] = []
distribute [] bs = []
distribute as bs = [normalisedProd a b | a <- as, b <- bs]

normProd :: ResourceTerm -> ResourceTerm
normProd (RTProd ts)
          | all isOne ts = RTId
          | otherwise    = RTProd ts
normProd t               = t

normalisedProd :: ResourceTerm -> ResourceTerm -> ResourceTerm
normalisedProd t s = combine (normProd s) (normProd t)
  where 
        combine RTId        s           = s
        combine t           RTId        = t
        combine (RTProd ts) (RTProd ss) = RTProd $ MSet.union ts ss
        combine t           (RTProd ss) = RTProd $ MSet.insert t ss
        combine (RTProd ts) s           = RTProd $ MSet.insert s ts
        combine t           s           = RTProd $ MSet.fromList [t, s]

normBinom :: SizeSum -> Int -> [ResourceTerm]
normBinom _ 0 = [RTId]
normBinom ss@(SizeSum coeffs c) k = case (M.keys coeffs, c) of
  ([x], 0) -> [RTBinom (sizeVar x) k]
  ([x], 1) -> RTBinom (sizeVar x) k :
              [case k - 1 of
                 0 -> RTId
                 _ -> RTBinom (sizeVar x) (k - 1)
              | k - 1 >= 0]
  (x : xs, 0)   -> concat
    [distribute
      [RTBinom (sizeVar x) r]
      (case (k - r) of
         0 -> [RTId]
         _ -> normBinom (sizeVars xs) (k - r)
      )
    | r <- [0..k]]
  ([], 0)       -> []
  (xs, c)       ->  error $ "cannot normalise arbitrary sums in binomial coeffients: " ++ show xs ++ show k

--------------------------------------------------------------------------------
-- Template Operations
--------------------------------------------------------------------------------


scale :: (Template a) => a -> ArithExpr -> ArithTemplate
scale q k = ArithTemplate $
  M.fromList [(term, C.prod2 (q!term) k) | term <- S.toList (terms q)]


add :: (Template a, Template b) => a -> b -> ArithTemplate
add q p = ArithTemplate $ M.fromList
  [(idx, C.sum [q!?idx, p!?idx])
  | idx <- S.toList $ terms q `S.union` terms p]
  

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
    
