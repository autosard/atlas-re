{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential where

import Prelude hiding (sum, (!))
import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S
import Lens.Micro.Platform


import Primitive(Id)
import CostAnalysis.Rules ( WeakenArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn
import Typing.Type (Type)
import Ast

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x


type ExpertKnowledge = (V.Vector (V.Vector Int), [Int])

data AnnRanges = AnnRanges {
  rangeA :: ![Int],
  rangeB :: ![Int],
  rangeBNeg :: ![Int]}

data PotentialMode
  = Logarithmic
  | Polynomial

data Potential = Potential {
  -- Supported types
  --types :: [Type],

  bearesPotential :: Type -> Bool,
  
  ranges :: AnnRanges,
  
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label comment vars (rangeA, rangeB) @ constructs a fresh resource annotation with arguments from @vars@ (types are considered). @rangeA@, @rangeB@ are used to define non-zero coefficients. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> Text -> [(Id, Type)] -> ([Int], [Int]) -> RsrcAnn, 

  -- | @ 'constCoeff'@ returns the coefficient index for the constant basic potential function.
  constCoeff :: CoeffIdx,

  -- | @ 'forAllCombinations' q xs (rangeA, rangeB) x@ generates an index for all combinations of variables in @xs@ and the variable @x@, based on the indices in @q@.
  forAllCombinations :: RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx],
  
  -- Constraint generation
  
  -- | @ 'cConst' q q'@ returns constraints that guarantee \[\phi(\Gamma \mid Q) = \phi(\Delta \mid Q') \text{ where } |\Gamma| = |Q|, |\Delta| = |Q'|\]  
  cConst :: PositionedExpr -> RsrcAnn -> RsrcAnn -> Either String [Constraint],
  -- | @ 'cMatch' q p_ x ys = (p, cs)@ defines @p@ with the empty annotation @p_@ from @q@ by constraints @cs@, guaranteeing \[\phi(\Gamma, x \mid Q) = \phi(\Gamma, \vec{y} \mid P)\] where @x@ is the variable that matched and @ys@ is the pattern variables.
  cMatch :: RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetBinding' q p_ = (p, cs)@
  cLetBindingBase :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetBodyBase' q r_ p' = (r, cs)@
  cLetBodyBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),

   -- | @ 'cLetBinding' q p_ = (p, cs)@
  cLetBinding :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetBody' q r_ p p' ps' x bdes = (r, cs)@
  cLetBody :: RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> AnnArray -> Id -> [CoeffIdx] -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetCf' q ps_ ps'_ x bdes = (ps, ps', cs)@
  cLetCf :: RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (AnnArray, AnnArray, [Constraint]),
    
  -- | @ 'cWeakenVar' q r @
  cWeakenVar :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),
  
  genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> ExpertKnowledge,
  
  -- | @ 'cOptimize' q q' @ returns a cost function that minimizes \[\Phi(\Gamma\mid Q) - \Phi(\Gamma\mid Q')\] as a term.
  cOptimize :: RsrcAnn -> RsrcAnn -> Term,
  
  printBasePot :: Coeff -> Rational -> String}

defaultNegAnn :: Potential -> Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn
defaultNegAnn pot id label comment args = rsrcAnn pot id label comment args abRanges
  where abRanges = (rangeA (ranges pot), rangeBNeg (ranges pot))
  
defaultAnn :: Potential -> Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn
defaultAnn pot id label comment args = rsrcAnn pot id label comment args abRanges 
  where abRanges = (rangeA (ranges pot), rangeB (ranges pot))

emptyAnn :: Potential -> Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn
emptyAnn pot id label comment args = RsrcAnn id args' label comment S.empty
  where args' = filter (\(x, t) -> bearesPotential pot t) args

enrichWithDefaults :: Potential -> Bool -> Int -> Text -> Text -> RsrcAnn -> RsrcAnn
enrichWithDefaults pot neg id label comment origin =
  RsrcAnn id args_ label comment ((origin^.coeffs) `S.union` defaultCoeffs)
  where args_ = origin^.args
        annGen = if neg then defaultNegAnn else defaultAnn
        defaultCoeffs = annGen pot id "" "" args_ ^.coeffs


eqExceptConst :: Potential -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
eqExceptConst pot q_ p = extendAnn q_ [(`eq` (p!idx)) <$> def idx
                                      | idx <- S.toList (p^.coeffs),
                                        idx /= constCoeff pot]

-- | @ 'eqPlus' q p t@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + t\] where @t@ is a term.
eqPlus :: Potential -> RsrcAnn -> RsrcAnn -> Term -> (RsrcAnn, [Constraint])
eqPlus pot q_ p t = (q, cs ++ eqCs)
  where constIdx = constCoeff pot
        (eqQ, eqCs) = eqExceptConst pot q_ p
        (q, cs) = extendAnn eqQ [(`eq` sum [p!?constIdx, t]) <$> def constIdx]

-- | @ 'eqMinus' q p t@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - t\] where @t@ is a term.
eqMinus :: Potential -> RsrcAnn -> RsrcAnn -> Term -> (RsrcAnn, [Constraint])
eqMinus pot q_ p t = (q, cs ++ eqCs)
  where constIdx = constCoeff pot
        (eqQ, eqCs) = eqExceptConst pot q_ p
        constP = p!?constIdx
        (q, cs) = case constP of
          (ConstTerm 0) -> (eqQ, [])
          _nonZero -> extendAnn eqQ [(`eq` sub [p!?constIdx, t]) <$> def constIdx]

--  -- | @ 'cPlusMulti' q p r k@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\].
-- cPlusMulti :: RsrcAnn -> RsrcAnn -> RsrcAnn -> Var -> [Constraint],
-- cPlusMulti q p r k = q `annEq` (annAdd p (annScalarMul r k))

calculateBound :: (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> Map Coeff Rational
calculateBound (from, to) solution = M.fromList $ map subtract (getCoeffs from)
  where solutionOrZero coeff = case solution M.!? coeff of
                                 Just value -> (coeff, value)
                                 Nothing -> (coeff, 0)           
        subtract left@(Coeff _ _ _ idx) = let
          right = if length (annVars from) == length (annVars to) then
            to!?substitute (annVars from) (annVars to) idx else to!?idx in
          case right of
            (CoeffTerm r) ->
              case solution M.!? r of
                Just rightValue -> case solution M.!? left of
                  Just leftValue -> let diff =  leftValue - rightValue in (left, diff)
                --if diff >= 0 then (left, diff) else error "Negative coefficient in result bound."
                  Nothing -> error $ "No such base term on the left hand side for '" ++ show right ++ "'."
                Nothing -> solutionOrZero left
            (ConstTerm 0) -> solutionOrZero left
  
symbolicCost :: (RsrcAnn, RsrcAnn) -> PointWiseOp
symbolicCost (from, to) = PointWiseOp (annVars from) $
  M.fromList [(idx, sub [from!idx, to!?idx'])
             | idx <- S.toList $ definedIdxs from,
               let idx' = if length (annVars from) == length (annVars to) then
                     substitute (annVars from) (annVars to) idx else idx]

printRHS :: Potential -> RsrcAnn -> Map Coeff Rational -> String
printRHS pot rhs solution = printPotential pot $ M.toList (M.restrictKeys solution (S.fromList (getCoeffs rhs)))

printPotential :: Potential -> [(Coeff, Rational)] -> String
printPotential pot coeffs = if L.null coeffs' then "0" else
  L.intercalate " + " $ map (uncurry (printBasePot pot)) coeffs'
  where coeffs' = filter (\(_, v) -> v /= 0) coeffs

printBound :: Potential -> (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> String
printBound pot sig solution = printPotential pot terms
  where terms = M.toList $ M.filter (0 /=) solution'
        solution' = calculateBound sig solution
  
