{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Template where

import Prelude hiding (sum, or, and)

import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.List as L
import Data.Text(Text)
import Lens.Micro.Platform
import Data.Maybe (fromMaybe)

import Primitive(Id, Substitution, traceShow, traceShowV)
import CostAnalysis.Coeff
import Control.Monad.State
import  CostAnalysis.Constraint(Term, Constraint, Term(..))
import qualified CostAnalysis.Constraint as C
import CostAnalysis.AnnIdxQuoter(mix)


class (Show a) => Template a where
  infixl 9 !
  (!) :: (Index i, Show i) => a -> i -> Term
  infixl 9 !?
  (!?) :: (Index i, Show i) => a -> i -> Term
  idxs :: a -> Set CoeffIdx
  args :: a -> [Id]
  empty :: a -> Bool
  merge :: a -> a -> a

mixes :: (Template a) => a -> [CoeffIdx]
mixes = S.toList . S.filter (not . isPure) . idxs



restrictFacs1 :: [CoeffIdx] -> [CoeffIdx]
restrictFacs1 = filter (onlyFacsOfLen 1)

restrictFacs2 :: [CoeffIdx] -> [CoeffIdx]
restrictFacs2 = filter (onlyFacsOfLen 2)

pures :: (Template a) => a -> [CoeffIdx]
pures = S.toList . S.filter isPure . idxs


data FreeTemplate = FreeTemplate {
  _ftId :: Int,
  _ftArgs :: [Id],
  _ftLabel :: Text, -- ^ Human readable label, e.g. \"Q\", \"P\", ...
  _ftComment ::  Text, -- ^ Human readable comment, to trace the origin of the coefficient.
  _ftCoeffs :: Set CoeffIdx -- ^ non zero coefficients
  }
  deriving (Eq, Show)

makeLenses ''FreeTemplate

instance Template FreeTemplate where
  args = _ftArgs
  idxs q = q^.ftCoeffs
  empty = S.null . _ftCoeffs
  (!) templ idx = case coeffForIdx templ (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> error $ "Invalid index '" ++ show idx ++ "' for template '" ++ show templ ++ "'."
  (!?) templ idx = case coeffForIdx templ (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> ConstTerm 0
  merge q p = FreeTemplate {
    _ftId = q^.ftId,
    _ftArgs = (q^.ftArgs) `L.union` (p^.ftArgs),
    _ftLabel = q^.ftLabel,
    _ftComment = q^.ftComment,
    _ftCoeffs = (q^.ftCoeffs) `S.union` (p^.ftCoeffs)}

coeffForIdx :: FreeTemplate -> CoeffIdx -> Maybe Coeff
coeffForIdx templ idx =
  if S.member idx (idxs templ) then
    Just $ coeffForTemplate templ idx
  else Nothing

coeffForTemplate :: FreeTemplate -> CoeffIdx -> Coeff
coeffForTemplate templ = Coeff (templ^.ftId) (templ^.ftLabel) (templ^.ftComment)

mixes1 :: (Template a) => a -> [CoeffIdx]
mixes1 q = filter (onlyFacsOfLen 1) $ mixes q

mixes2 :: (Template a) => a -> [CoeffIdx] 
mixes2 q = filter (\idx -> onlyFacsOfLen 2 idx && (not . justConst) idx) $ mixes q

mixesForVars :: (Template a) => a -> [Id] -> [CoeffIdx] 
mixesForVars ann xs = S.toList $ S.map (mixed . (`varsRestrict` xs)) . S.filter (not . isPure) $ idxs ann

mixesForVars1 :: (Template a) => a -> [Id] -> [CoeffIdx] 
mixesForVars1 ann xs = S.toList $ S.map (mixed . (`varsRestrict` xs)) $ S.fromList (mixes1 ann)

mixesForVars2 :: (Template a) => a -> [Id] -> [CoeffIdx] 
mixesForVars2 ann xs = S.toList $ S.map (mixed . (`varsRestrict` xs)) $ S.fromList (mixes2 ann)



instance HasCoeffs FreeTemplate where
  getCoeffs templ = map (coeffForTemplate templ) $ S.toList (templ^.ftCoeffs)


defineFrom :: Int -> Text -> Text -> FreeTemplate -> FreeTemplate
defineFrom id label comment templ = FreeTemplate id (templ^.ftArgs) label comment (templ^.ftCoeffs)

substArg :: Id -> Id -> FreeTemplate -> FreeTemplate
substArg x y q = q
  & ftArgs .~ args'
  & ftCoeffs %~ S.map (substitute (q ^. ftArgs) args') 
  where args' = map (\z -> if z == x then y else z) $ q ^. ftArgs

data BoundTemplate = BoundTemplate [Id] (Map CoeffIdx Rational)
  deriving (Eq, Show)

instance Template BoundTemplate where
  args (BoundTemplate vars _) = vars
  idxs (BoundTemplate _ m) = M.keysSet m
  empty (BoundTemplate _ m) = M.null m
  (!) (BoundTemplate _ m) idx = ConstTerm $ m M.! toIdx idx
  (!?) (BoundTemplate _ m) idx = ConstTerm $ fromMaybe 0 (m M.!? toIdx idx)
  merge (BoundTemplate xs ma) (BoundTemplate ys mb)
    = BoundTemplate (xs `L.union` ys) (M.union ma mb)

bindTemplate :: FreeTemplate -> Map Coeff Rational -> BoundTemplate
bindTemplate q values = BoundTemplate
  (args q)
  (M.fromList [(i, v)
              | c@(Coeff _ _ _ i) <- getCoeffs q,
                let v = fromMaybe 0 (values M.!? c)])

split :: BoundTemplate -> [Id] -> (BoundTemplate, BoundTemplate)
split (BoundTemplate args coeffs) argsY =
  let argsX = (args L.\\ argsY)
      x = BoundTemplate argsX
        (M.filterWithKey (\idx _ -> hasArgsOrConst argsX idx) coeffs)
      y = BoundTemplate argsY
        (M.filterWithKey (\idx _ -> hasArgs argsY idx && (not . idxNull) idx) coeffs) in
    (x,y)
                                    

addValues :: BoundTemplate -> BoundTemplate -> BoundTemplate
addValues q@(BoundTemplate argsQ qIs) p@(BoundTemplate argsP pIs)
  = BoundTemplate (argsQ `L.union` argsP)
    (M.fromList [(idx, fromMaybe 0 (qIs M.!? idx)
                       + fromMaybe 0 (pIs M.!? idx))
                | idx <- S.toList $ idxs q `S.union` idxs p])

data TermTemplate = TermTemplate {
  ttArgs :: [Id] ,
  terms :: Map CoeffIdx Term}
  deriving(Show)

instance Template TermTemplate where
  args = ttArgs
  idxs templ =  M.keysSet $ terms templ
  empty = M.null . terms
  (!) templ idx = terms templ M.! toIdx idx
  (!?) templ idx = fromMaybe (ConstTerm 0) $ terms templ M.!? toIdx idx
  merge (TermTemplate argsA termsA) (TermTemplate argsB termsB)
    = TermTemplate (argsA `L.union` argsB) (M.union termsA termsB)

zeroTemplate = TermTemplate [] M.empty


-- operations

scale :: (Template a) => a -> Term -> TermTemplate
scale q k = TermTemplate (args q) $
  M.fromList [(idx, C.prod2 (q!idx) k) | idx <- S.toList (idxs q)]

add :: (Template a, Template b) => a -> b -> TermTemplate
add q p = TermTemplate (args q `L.union` args p) $
             M.fromList [(idx, C.sum [q!?idx, p!?idx])
                        | idx <- S.toList $ idxs q `S.union` idxs p]

sub :: (Template a, Template b) => a -> b -> TermTemplate
sub q p = TermTemplate (args q `L.union` args p) $
             M.fromList [(idx, C.sub [q!?idx, p!?idx])
                        | idx <- S.toList $ idxs q `S.union` idxs p]

sum :: (Template a) => a -> Term
sum q = C.sum [q!i | i <- S.toList $ idxs q]

assertEq :: (Template a, Template b) => a -> b -> [Constraint]
assertEq q p = concat [C.eq (q!?idx) (p!?idx) | idx <- S.toList $ idxs q `S.union` idxs p]

assertLe :: (Template a, Template b) => a -> b -> [Constraint]
assertLe q p = concat [C.le (q!?idx) (p!?idx) | idx <- S.toList $ idxs q `S.union` idxs p]

assertGe :: (Template a, Template b) => a -> b -> [Constraint]
assertGe q p = concat [C.ge (q!?idx) (p!?idx) | idx <- S.toList $ idxs q `S.union` idxs p]

assertGeZero :: Template a => a -> [Constraint]
assertGeZero = (`assertGe` zeroTemplate)

assertZero :: Template a => a -> [Constraint]
assertZero = (`assertEq` zeroTemplate)

assertZeroExcept :: Template a => a -> Set CoeffIdx -> [Constraint]
assertZeroExcept q except = concat [ if idx `S.member` except
                                     then C.eq (q!idx) (ConstTerm 1)
                                     else C.zero (q!idx)
                                   | idx <- S.toList $ idxs q]

unifyAssertEq :: (Template a, Template b) => a -> b -> [Constraint]
unifyAssertEq q p = concat [C.eq (q!?idx) p'
                          | idx <- S.toList $ idxs q,
                            let p' | justConst idx = p!?idx 
                                   | length (args q) == length (args p) 
                                  = p!?substitute (args q) (args p) idx
                                   | otherwise = ConstTerm 0]
                  
unifyAssertEqBy :: (Template a, Template b) => a -> b -> [Id] -> [Constraint]
unifyAssertEqBy q p qArgs = concat [C.eq (q!?idx) (p!?substitute qArgs (args p) idx)
                                 | idx <- S.toList $ idxs q]

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
apply :: (Template a, Template b) => a -> b -> Map CoeffIdx CoeffIdx
apply q p | length (args q) == length (args p) =
            let s = M.fromList (zip (args q) (args p)) in
              M.fromList [(i, substitute (args q) (args p) i) | i <- S.toList (idxs q)]
apply q p = case args p of
              [] -> M.empty
              [y] -> M.fromList [(i, substitute (args q)
                                   (replicate (length (args q)) y) i)
                                | i <- S.toList (idxs q),
                                  isPure i || justConst i || singleVar i]
              _ys_greater_xs -> error $ "cannot apply potential function " ++ show p ++ " to arguments " ++ show (args q)

symbolicCost :: (Template a, Template b) => a -> b -> TermTemplate
symbolicCost q p = TermTemplate (args q) $  
  M.fromList [(idx, C.sub [q!idx, tP]) 
             | idx <- S.toList $ idxs q,
               let tP = maybe (ConstTerm 0) (p!?) (u M.!? idx)] 
  where u = apply q p

calculateBound :: ((FreeTemplate, FreeTemplate), FreeTemplate) -> Map Coeff Rational -> BoundTemplate
calculateBound ((from, fromRef), to) solution =
  let diff = BoundTemplate (args from) $ M.fromList
        [(idx, from' M.! idx - fromMaybe 0 ((to' M.!?) =<< (u M.!? idx)))
        | idx <- S.toList $ idxs from] in
    addValues diff qe
  where q@(BoundTemplate _ from') = bindTemplate from solution
        qe = bindTemplate fromRef solution
        p@(BoundTemplate _ to') = bindTemplate to solution
        u = apply q p

-- array

type TemplateArray = Map CoeffIdx FreeTemplate

elems :: TemplateArray -> [FreeTemplate]
elems = M.elems

infixl 9 !!
(!!) :: TemplateArray -> CoeffIdx -> FreeTemplate
(!!) arr k = case M.lookup k arr of
  Just c -> c
  Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation array."


type CoeffDef s a = State s a

def :: Index i => i -> CoeffDef FreeTemplate Term
def i = do
  let idx = toIdx i
  ftCoeffs %= (idx `S.insert`)
  templ <- get
  return $ templ!idx

def2 :: (Index i, Index j) => i -> j -> CoeffDef FreeTemplate Term
def2 i j = do
  let idx1 = toIdx i
  let idx2 = toIdx j
  ftCoeffs %= (idx1 `S.insert`)
  ftCoeffs %= (idx2 `S.insert`)
  templ <- get
  return $ C.sum [templ!idx1, templ!idx2]

chainDef :: [a -> (a, [Constraint])] -> a -> (a, [Constraint])
chainDef fs q_ = foldr go (q_, []) fs
  where go f (q, css) = let (q', cs) = f q in
          (q', cs ++ css)

defEntry :: CoeffIdx -> CoeffIdx -> CoeffDef TemplateArray Term
defEntry arrIdx coeffIdx = do
  ix arrIdx . ftCoeffs %= (coeffIdx `S.insert`)
  arr <- get
  return $ (arr M.! arrIdx)!coeffIdx

extend :: a -> [CoeffDef a [Constraint]] -> (a, [Constraint])
extend ann defs = (ann', concat cs)
  where (cs, ann') = runState def ann
        def = sequence defs
        
extends :: TemplateArray -> [CoeffDef TemplateArray [a]] -> (TemplateArray, [a])
extends arr defs = (arr', concat cs)
  where (cs, arr') = runState def arr
        def = sequence defs
  
defineBy :: FreeTemplate -> FreeTemplate -> (FreeTemplate, [Constraint])
defineBy q p = defineByWith q p (const C.eq)

-- | @'defineFrom' q p f@ Define q from p. This sets q(x) = p(x), where x contains only variables from q. If x is constant coefficient the function f is applied instead of euqality, i.e. f q(idx) p(idx).
defineByWith :: FreeTemplate -> FreeTemplate -> (CoeffIdx -> Term -> Term -> [Constraint])
  -> (FreeTemplate, [Constraint])
defineByWith q p f = let xs = args q in
  extend q $
  [(`C.eq` (p!idx)) <$> def idx
  | idx@(Pure x) <- pures p,
    x `elem` xs]
  ++ 
  [(`C.eq` (p!idx)) <$> def idx
  | idx <- mixes p,
    (not . justConst) idx,
    onlyVarsOrConst idx xs]
  ++
  [flip (f idx) (p!idx) <$> def idx
  | idx <- mixes p,
    justConst idx]

rhs :: Id
rhs = "e1"

cLetBodyUni :: FreeTemplate -> FreeTemplate -> FreeTemplate
  -> Id -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyUni q p p' x r_ = extend r_ $
  [(`C.eq` (q!y)) <$> def y
  | idx@(Pure y) <- pures q,
    y `elem` ys]
  ++ [(`C.eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx ys,
       (not . justConst) idx]
  -- move const
  ++ [(`C.eq` C.sum [C.sub [q!?idx, p!idx], p'!?idx]) <$> def idx
     | idx <- mixes q,
       justConst idx]
  
  ++ [(`C.eq` (p'!rhs)) <$> def x | (p'!?rhs) /= ConstTerm 0]
  ++ [(`C.eq` (p'!pIdx)) <$> def [mix|x^d,e|]
     | pIdx <- mixes p',
       let d = facForVar pIdx rhs,
       let e = constFactor pIdx,
       let rIdx = [mix|x^d,e|],
       (not . justConst) rIdx]
  where ys = L.delete x (args r_)

nonBindingMultiGeZero :: FreeTemplate -> [Id] -> [Id] -> [Constraint]
nonBindingMultiGeZero q gamma delta = concat $
  [C.geZero (q!idx) 
  | idx <- mixes q,
    containsArgs gamma idx && containsArgs delta idx,
    not . justConst $ idx]

share :: FreeTemplate -> FreeTemplate -> [Id] -> Substitution -> Substitution -> (FreeTemplate, [Constraint]) 
share q p_ zs s1 s2 =
  let (pCommon_, csCommon) =
        extend p_ [(`C.eq` (q!idx)) <$> def idx
                          | idx <- S.toList (idxs q),
                            not (containsArgs zs idx)]
      (p, cs) =
        extend pCommon_ [(`C.eq` (q!idx)) <$> def2 idx1 idx2
                          | idx <- S.toList (idxs q),
                            containsArgs zs idx,
                            let idx1 = substitute' s1 idx,
                            let idx2 = substitute' s2 idx] in
    (p, cs ++ csCommon)
