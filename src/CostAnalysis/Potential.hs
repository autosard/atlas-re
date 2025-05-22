{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential where

import Prelude hiding (sum, (!), (!!), exp)
import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S
import Lens.Micro.Platform


import Primitive(Id, printRat)
import CostAnalysis.Rules ( WeakenArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn
import Typing.Type (Type)
import Ast hiding (FunRsrcAnn)
import CostAnalysis.AnnIdxQuoter(mix)

import Data.Maybe (fromMaybe)

type LeMatrix = (V.Vector (V.Vector Rational), [Rational])

data ExpertKnowledge = ExpertKnowledge {
  matrix :: LeMatrix,
  rows :: !(V.Vector (CoeffIdx, Term)),
  cols :: !(V.Vector (CoeffIdx, Term))}

type PotFnMap = Map Type (Potential, RsrcAnn)

data AnnRanges = AnnRanges {
  rangeA :: ![Int],
  rangeB :: ![Int],
  rangeBNeg :: ![Int]}


data MonoFn = Log
  deriving (Enum, Bounded)


data Potential = Potential {
  -- Annotation
  
  -- | @ 'rsrcAnn' id label comment vars (rangeA, rangeB) @ constructs a fresh resource annotation with arguments from @vars@ (types are considered). @rangeA@, @rangeB@ are used to define non-zero coefficients. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> RsrcAnn,

  ranges :: AnnRanges,

  -- | @ 'oneCoeff'@ returns the coefficient index for the constant basic potential function.
  oneCoeff :: CoeffIdx,

  zeroCoeff :: Maybe CoeffIdx,

  -- | @ 'monoFnCoeff fn args c' returns the coefficient index of the given monotonic basic potential function 'fn' with arguments 'args', with shift 'c'. If the function is not present, 'Nothing' is returned.
  monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx,

  -- Constraints
  
  -- | @ 'cConst' q q'@ returns constraints that guarantee \[\phi(\Gamma \mid Q) = \phi(\Delta \mid Q') \text{ where } |\Gamma| = |Q|, |\Delta| = |Q'|\]  
  cConst :: PositionedExpr -> RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cMatch' q p_ x ys = (p, cs)@ defines @p@ with the empty annotation @p_@ from @q@ by constraints @cs@, guaranteeing \[\phi(\Gamma, x \mid Q) = \phi(\Gamma, \vec{y} \mid P)\] where @x@ is the variable that matched and @ys@ is the pattern variables.
  cMatch :: RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint]),

  -- | @ 'letBodyMulti' q ps' x is r_ = (r, cs)@
  cLetBodyMulti :: RsrcAnn -> AnnArray -> Id -> [CoeffIdx] -> RsrcAnn -> (RsrcAnn, [Constraint]),

  -- | @ 'letCfIdxs' q xs (rangeA, rangeB) x@ generates an index for every cf derivation in the rule from the indices in @q@ and the given ranges.
  letCfIdxs :: RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx],

  -- | @ 'cLetCf' q ps_ ps'_ x is = (ps, ps', cs)@
  cLetCf :: RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (AnnArray, AnnArray, [Constraint]),

  genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> LeMatrix,

  -- | @ 'cExternal' q q' @ returns constraints over the annoations q and q'. 
  cExternal :: RsrcAnn -> RsrcAnn -> [Constraint],
  
  -- | @ 'cOptimize' q q' @ returns a cost function that minimizes \[\Phi(\Gamma\mid Q) - \Phi(\Gamma\mid Q')\] as a term.
  cOptimize :: RsrcAnn -> RsrcAnn -> Term,
  
  printBasePot :: CoeffIdx -> String}

defaultNegAnn :: Potential -> Int -> Text -> Text -> [Id] -> RsrcAnn
defaultNegAnn pot id label comment args = rsrcAnn pot id label comment args abRanges
  where abRanges = (rangeA (ranges pot), rangeBNeg (ranges pot))
  
defaultAnn :: Potential -> Int -> Text -> Text -> [Id] -> RsrcAnn
defaultAnn pot id label comment args = rsrcAnn pot id label comment args abRanges 
  where abRanges = (rangeA (ranges pot), rangeB (ranges pot))

emptyAnn :: Potential -> Int -> Text -> Text -> [Id] -> RsrcAnn
emptyAnn pot id label comment args = RsrcAnn id args label comment S.empty

enrichWithDefaults :: Potential -> Bool -> Int -> Text -> Text -> RsrcAnn -> RsrcAnn
enrichWithDefaults pot neg id label comment origin =
  RsrcAnn id args_ label comment ((origin^.coeffs) `S.union` defaultCoeffs)
  where args_ = origin^.args
        annGen = if neg then defaultNegAnn else defaultAnn
        defaultCoeffs = annGen pot id "" "" args_ ^.coeffs

defineBody :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
defineBody r_ q p = defineFrom' r_ q constConstraint
  where constConstraint idx r q = r `eq` sub [q, p!idx]

-- | @'defineFrom' pot q p f@ Define q from p. This sets q(x) = p(x), where x contains only variables from q. If x is constant coefficient the function f is applied instead of euqality, i.e. f q(idx) p(idx).
defineFrom' :: RsrcAnn -> RsrcAnn -> (CoeffIdx -> Term -> Term -> [Constraint])
  -> (RsrcAnn, [Constraint])
defineFrom' q p f = let xs = annVars q in
  extendAnn q $
  [(`eq` (p!idx)) <$> def idx
  | idx@(Pure x) <- pures p,
    x `elem` xs]
  ++ 
  [(`eq` (p!idx)) <$> def idx
  | idx <- mixes p,
    (not . justConst) idx,
    onlyVarsOrConst idx xs]
  ++
  [flip (f idx) (p!idx) <$> def idx
  | idx <- mixes p,
    justConst idx]

eqExceptConst :: Potential -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
eqExceptConst pot q_ p = extendAnn q_ [(`eq` (p!idx)) <$> def idx
                                      | idx <- S.toList (p^.coeffs),
                                        idx /= oneCoeff pot]

-- | @ 'eqPlus' q p t@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + t\] where @t@ is a term.
eqPlus :: Potential -> RsrcAnn -> RsrcAnn -> Term -> (RsrcAnn, [Constraint])
eqPlus pot q_ p t = (q, cs ++ eqCs)
  where constIdx = oneCoeff pot
        (eqQ, eqCs) = eqExceptConst pot q_ p
        (q, cs) = extendAnn eqQ [(`eq` sum [p!?constIdx, t]) <$> def constIdx]

-- | @ 'eqMinus' q p t@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - t\] where @t@ is a term.
eqMinus :: Potential -> RsrcAnn -> RsrcAnn -> Term -> (RsrcAnn, [Constraint])
eqMinus pot q_ p t = (q, cs ++ eqCs)
  where constIdx = oneCoeff pot
        (eqQ, eqCs) = eqExceptConst pot q_ p
        constP = p!?constIdx
        (q, cs) = case constP of
          (ConstTerm 0) -> (eqQ, [])
          _nonZero -> extendAnn eqQ [(`eq` sub [p!?constIdx, t]) <$> def constIdx]

exp :: Id
exp = "e1"

cLetBodyUni :: RsrcAnn -> RsrcAnn -> RsrcAnn
  -> Id -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyUni q p p' x r_ = extendAnn r_ $
  [(`eq` (q!y)) <$> def y
  | idx@(Pure y) <- pures q,
    y `elem` ys]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx ys,
       (not . justConst) idx]
  -- move const
  ++ [(`eq` sum [sub [q!?idx, p!idx], p'!?idx]) <$> def idx
     | idx <- mixes q,
       justConst idx]
  
  ++ [(`eq` (p'!exp)) <$> def x | (p'!?exp) /= ConstTerm 0]
  ++ [(`eq` (p'!pIdx)) <$> def [mix|x^d,e|]
     | pIdx <- mixes p',
       let d = facForVar pIdx exp,
       let e = constFactor pIdx,
       let rIdx = [mix|x^d,e|],
       (not . justConst) rIdx]
  where ys = L.delete x (annVars r_)

calculateBound :: (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> BoundAnn
calculateBound (from, to) solution = BoundAnn (from^.args) $ M.fromList
  [(idx, from' M.! idx - fromMaybe 0 ((to' M.!?) =<< (u M.!? idx)))
  | idx <- S.toList $ definedIdxs from']
  where q@(BoundAnn _ from') = bindAnn from solution
        p@(BoundAnn _ to') = bindAnn to solution
        u = unify q p
  
symbolicCost :: (AnnLike a, AnnLike b) => a -> b -> PointWiseOp
symbolicCost q p = PointWiseOp (argVars q) $  
  M.fromList [(idx, sub [q!idx, tP])
             | idx <- S.toList $ definedIdxs q,
               let tP = maybe (ConstTerm 0) (p!?) (u M.!? idx)]
  where u = unify q p
             
ctxSymbolicCost :: (AnnLike a, AnnLike b) => (Map Type a, Map Type b) -> Map Type PointWiseOp
ctxSymbolicCost (from, to) = ctxZipWith
  (const (`symbolicCost` pointWiseZero))
  (const (symbolicCost pointWiseZero))
  (const symbolicCost) from to

printRHS :: Potential -> RsrcAnn -> Map Coeff Rational -> String
printRHS pot rhs solution = printPotential pot $ bindAnn rhs solution

printBound :: PotFnMap -> (AnnCtx, AnnCtx) -> Map Coeff Rational -> String
printBound pots (from, to) solution = L.intercalate " + " bounds
  where bounds = filter (/= "0") (map costForType (M.keys from))
        costForType :: Type -> String
        costForType t = let pot = fst $ pots M.! t
                            to' = fromMaybe (emptyAnn pot 0 "" "" []) $ to M.!? t
                            from' = fromMaybe (emptyAnn pot 0 "" "" []) $ from M.!? t
                            bound = calculateBound (from', to') solution in
                          printPotential pot bound

printPotential :: Potential -> BoundAnn -> String
printPotential pot (BoundAnn _ coeffs) = if M.null coeffs' then "0" else
  L.intercalate " + " $
    map (uncurry (printPotTerm pot)) (M.assocs coeffs')
  where coeffs' = M.filter (/= 0) coeffs
        
  
printPotTerm :: Potential -> CoeffIdx -> Rational -> String
printPotTerm pot c 1 = if c == oneCoeff pot then "1" else printBasePot pot c
printPotTerm pot c v | c == oneCoeff pot = printRat v
                     | otherwise = printRat v ++ " * " ++ printBasePot pot c

