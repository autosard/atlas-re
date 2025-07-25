{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential where

import Prelude hiding (sum, (!), (!!), exp)
import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S


import Primitive(Id, printRat)
import CostAnalysis.Rules ( WeakenArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Annotation
import CostAnalysis.Template (Template(..),
                              FreeTemplate(..),
                              BoundTemplate(..),
                              TemplateArray,
                              calculateBound,
                              bindTemplate)
import qualified CostAnalysis.Template as Templ
import Typing.Type (Type)
import Ast hiding (FunRsrcAnn)

import Data.Maybe (fromMaybe)
import CostAnalysis.Predicate (Predicate)

type LeMatrix = (V.Vector (V.Vector Rational), [Rational])

data ExpertKnowledge = ExpertKnowledge {
  matrix :: LeMatrix,
  rows :: !(V.Vector (CoeffIdx, Term)),
  cols :: !(V.Vector (CoeffIdx, Term))}

type PotFnMap = Map Type (Potential, FreeTemplate)

data AnnRanges = AnnRanges {
  rangeA :: ![Int],
  rangeB :: ![Int],
  rangeBNeg :: ![Int]}


data MonoFn = Log
  deriving (Enum, Bounded)


data Potential = Potential {
  -- Annotation
  
  -- | @ 'template' id label comment vars (rangeA, rangeB) @ constructs a fresh function template with arguments from @vars@ (types are considered). @rangeA@, @rangeB@ are used to define non-zero coefficients. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  template :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> FreeTemplate,

  ranges :: AnnRanges,

  -- | @ 'oneCoeff'@ returns the coefficient index for the constant basic potential function.
  oneCoeff :: CoeffIdx,

  zeroCoeff :: Maybe CoeffIdx,

  -- | @ 'monoFnCoeff fn args c' returns the coefficient index of the given monotonic basic potential function 'fn' with arguments 'args', with shift 'c'. If the function is not present, 'Nothing' is returned.
  monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx,

  -- Constraints
  
  -- | @ 'cConst' q q'@ returns constraints that guarantee \[\phi(\Gamma \mid Q) = \phi(\Delta \mid Q') \text{ where } |\Gamma| = |Q|, |\Delta| = |Q'|\]  
  cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint],
  -- | @ 'cMatch' q p_ x ys = (p, cs)@ defines @p@ with the empty annotation @p_@ from @q@ by constraints @cs@, guaranteeing \[\phi(\Gamma, x \mid Q) = \phi(\Gamma, \vec{y} \mid P)\] where @x@ is the variable that matched and @ys@ is the pattern variables.
  cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint]),

  constCases :: Pattern Positioned -> [Predicate],

  -- | @ 'letBodyMulti' q ps' x is r_ = (r, cs)@
  cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint]),

  -- | @ 'letCfIdxs' q xs (rangeA, rangeB) x@ generates an index for every cf derivation in the rule from the indices in @q@ and the given ranges.
  letCfIdxs :: FreeTemplate -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx],

  -- | @ 'cLetCf' q ps_ ps'_ x is = (ps, ps', cs)@
  cLetCf :: FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint]),

  genExpertKnowledge :: Set WeakenArg -> Set Predicate -> [Id] -> Set CoeffIdx -> LeMatrix,

  -- | @ 'cExternal' q q' @ returns constraints over the annoations q and q'. 
  cExternal :: FreeTemplate -> FreeTemplate -> [Constraint],
  
  -- | @ 'cOptimize' (q, qe) q' @ returns a cost function that minimizes \[\Phi(\Gamma\mid Q) - \Phi(\Gamma\mid Q')\] as a term.
  cOptimize :: (FreeTemplate, FreeTemplate) -> FreeTemplate -> Term,
  
  printBasePot :: CoeffIdx -> String}

defaultNegTempl :: Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate
defaultNegTempl pot id label comment args = template pot id label comment args abRanges
  where abRanges = (rangeA (ranges pot), rangeBNeg (ranges pot))
  
defaultTempl :: Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate
defaultTempl pot id label comment args = template pot id label comment args abRanges 
  where abRanges = (rangeA (ranges pot), rangeB (ranges pot))

emptyAnn :: Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate
emptyAnn pot id label comment args = FreeTemplate id args label comment S.empty

enrichWithDefaults :: Potential -> Bool -> Int -> Text -> Text -> FreeTemplate -> FreeTemplate
enrichWithDefaults pot neg id label comment origin =
  FreeTemplate id (args origin) label comment (idxs origin `S.union` idxs
                                               (templGen pot id "" "" (args origin)))
  where templGen = if neg then defaultNegTempl else defaultTempl


defineByExceptConst :: Potential -> FreeTemplate -> FreeTemplate -> (FreeTemplate, [Constraint])
defineByExceptConst pot q_ p = Templ.extend q_ [(`eq` (p!idx)) <$> Templ.def idx
                                               | idx <- S.toList (idxs p),
                                                 idx /= oneCoeff pot]
                                        
-- -- | @ 'eqPlus' q p t@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + t\] where @t@ is a term.
-- eqPlus :: Potential -> FreeTemplate -> FreeTemplate -> Term -> (FreeTemplate, [Constraint])
-- eqPlus pot q_ p t = (q, cs ++ eqCs)
--   where constIdx = oneCoeff pot
--         (eqQ, eqCs) = eqExceptConst pot q_ p
--         (q, cs) = extendAnn eqQ [(`eq` sum [p!?constIdx, t]) <$> def constIdx]

-- -- | @ 'eqMinus' q p t@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - t\] where @t@ is a term.
-- eqMinus :: Potential -> FreeTemplate -> FreeTemplate -> Term -> (FreeTemplate, [Constraint])
-- eqMinus pot q_ p t = (q, cs ++ eqCs)
--   where constIdx = oneCoeff pot
--         (eqQ, eqCs) = eqExceptConst pot q_ p
--         constP = p!?constIdx
--         (q, cs) = case constP of
--           (ConstTerm 0) -> (eqQ, [])
--           _nonZero -> extendAnn eqQ [(`eq` sub [p!?constIdx, t]) <$> def constIdx]

printRHS :: Potential -> FreeTemplate -> Map Coeff Rational -> String
printRHS pot rhs solution = printPotential pot $ bindTemplate rhs solution

printBound :: PotFnMap -> ((FreeAnn, FreeAnn), FreeAnn) -> Map Coeff Rational -> String
printBound pots ((from, fromRef), to) solution =
  let bound = L.intercalate " + " bounds in
    if null bound then "0" else bound
  where bounds = filter (/= "0") (map costForType (M.keys from))
        costForType :: Type -> String
        costForType t = let pot = fst $ pots M.! t
                            to' = fromMaybe (emptyAnn pot 0 "" "" []) $ to M.!? t
                            from' = fromMaybe (emptyAnn pot 0 "" "" []) $ from M.!? t
                            fromRef' = fromMaybe (emptyAnn pot 0 "" "" []) $ fromRef M.!? t
                            bound = calculateBound ((from', fromRef'), to') solution in
                          printPotential pot bound

printPotential :: Potential -> BoundTemplate -> String
printPotential pot (BoundTemplate _ coeffs) = if M.null coeffs' then "0" else
  L.intercalate " + " $
    map (uncurry (printPotTerm pot)) (M.assocs coeffs')
  where coeffs' = M.filter (/= 0) coeffs
        
  
printPotTerm :: Potential -> CoeffIdx -> Rational -> String
printPotTerm pot c 1 = if c == oneCoeff pot then "1" else printBasePot pot c
printPotTerm pot c v | c == oneCoeff pot = printRat v
                     | otherwise = printRat v ++ " * " ++ printBasePot pot c

