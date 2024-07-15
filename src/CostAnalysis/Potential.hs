{-# LANGUAGE StrictData #-}

module CostAnalysis.Potential where

import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as M
import Data.List(intercalate)
import Prelude hiding ((!))

import Primitive(Id)
import CostAnalysis.Rules ( RuleArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization (OptiMonad, Target)
import CostAnalysis.RsrcAnn
import Typing.Type


data Potential = Potential {
  -- Supported types
  types :: [Type],
  
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label vars@ constructs a fresh resource annotation with tree arguments from @vars@. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> [(Id, Type)] -> RsrcAnn,
  
  -- | @ 'forAllIdx' neg xs x id label ys@ for all combinations of variables in @xs@ with the var @x@, construct a fresh annotation starting with id @id@ and with vars in @ys@. @neg@ allows negative constants. Returns the last used id + 1. 
  forAllCombinations :: Bool -> [(Id, Type)] -> Id -> Int -> Text -> [(Id, Type)] -> (AnnArray, Int),
  
  -- | @ 'elems' a@ converts an annotation array to a list.
  elems :: AnnArray -> [RsrcAnn],

  
  -- Constraint generation
  
  -- | @ 'cPlusConst' q p c@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + c\] where @c@ is constant.
  cPlusConst :: RsrcAnn -> RsrcAnn -> Rational -> [Constraint],
  -- | @ 'cMinusVar' q p@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - k\] where @k@ is a fresh variable.
  cMinusVar :: RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cPlusMulti' q p r@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\] where @k@ is a fresh variable.
  cPlusMulti :: RsrcAnn -> RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cEq' q q'@ returns constraints that guarantee \[\phi(\Gamma \mid Q) = \phi(\Delta \mid Q') \text{ where } |\Gamma| = |Q|, |\Delta| = |Q'|\]  
  cEq :: RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cMatch' q p x ys@ returns constraints that guarantee \[\phi(\Gamma, x \mid Q) = \phi(\Gamma, \vec{y} \mid P)\] where @x@ is the variable that matched and @ys@ is the pattern variables.
  cMatch :: RsrcAnn -> RsrcAnn -> Id -> [(Id, Type)] -> [Constraint],
  -- | @ 'cLetBase' q p r p'@
  cLetBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cLet' q p p' ps ps' r x@
  cLet :: Bool -> RsrcAnn -> RsrcAnn -> RsrcAnn
    -> AnnArray -> AnnArray -> RsrcAnn -> Id -> [Constraint],
  -- | @ 'cWeakenVar' q r @
  cWeakenVar :: RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cWeaken' q q' p p'@
  cWeaken :: [RuleArg] -> RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cOptimize' q q' @ returns constraints that minimize \[\Phi(\Gamma\mid Q) - \Phi(\Gamma\mid Q')\]
  cOptimize :: RsrcAnn -> RsrcAnn -> OptiMonad Target,
  
  printBasePot :: Coeff -> Rational -> String}


calculateBound :: (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> Map Coeff Rational
calculateBound (from, to) solution = M.fromList $ map subtract (getCoeffs from)
  where [arg] = annVars to
        subtract left@(AnnCoeff _ _ _ idx) = let
          right = to!substitute idx arg in
          case solution M.!? right of
            Just rightValue -> case solution M.!? left of
              Just leftValue -> let diff =  leftValue - rightValue in (left, diff)
                --if diff >= 0 then (left, diff) else error "Negative coefficient in result bound."
              Nothing -> error $ "No such base term on the left hand side for '" ++ show right ++ "'."
            Nothing -> case solution M.!? left of
              Just leftValue -> (left, leftValue)
              Nothing -> (left, 0)
            

printBound :: Potential -> (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> String
printBound pot sig solution = intercalate " + " $ map (uncurry (printBasePot pot)) (M.toList solution')
  where solution' = calculateBound sig solution
  
