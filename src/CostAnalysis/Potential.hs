{-# LANGUAGE StrictData #-}

module CostAnalysis.Potential where
import Data.Text(Text)
import Primitive(Id)

import CostAnalysis.Rules ( RuleArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization (OptiMonad, Target)
import CostAnalysis.RsrcAnn
import Typing.Type


data Potential a = Potential {
  -- Supported types
  types :: [Type],
  
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label vars@ constructs a fresh resource annotation with tree arguments from @vars@. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> [(Id, Type)] -> RsrcAnn a,
  
  -- | @ 'forAllIdx' neg xs x id label ys@ for all combinations of variables in @xs@ with the var @x@, construct a fresh annotation starting with id @id@ and with vars in @ys@. @neg@ allows negative constants. Returns the last used id + 1. 
  forAllCombinations :: Bool -> [Id] -> Id -> Int -> Text -> [(Id, Type)] -> (AnnArray (RsrcAnn a), Int),
  
  -- | @ 'elems' a@ converts an annotation array to a list.
  elems :: AnnArray (RsrcAnn a) -> [RsrcAnn a],

  
  -- Constraint generation
  
  -- | @ 'cPlusConst' q p c@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + c\] where @c@ is constant.
  cPlusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusVar' q p@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - k\] where @k@ is RsrcAnn a fresh variable.
  cMinusVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cPlusMulti' q p r@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\] where @k@ is a fresh variable.
  cPlusMulti :: RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cEq' q q'@ returns constraints that guarantee \[\phi(\Gamma \mid Q) = \phi(\Delta \mid Q') \text{ where } |\Gamma| = |Q|, |\Delta| = |Q'|\]  
  cEq :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cMatch' q p x ys@ returns constraints that guarantee \[\phi(\Gamma, x \mid Q) = \phi(\Gamma, \vec{y} \mid P)\] where @x@ is the variable that matched and @ys@ is the pattern variables.
  cMatch :: RsrcAnn a -> RsrcAnn a -> Id -> [(Id, Type)] -> [Constraint],
  -- | @ 'cLetBase' q p r p'@
  cLetBase :: RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cLet' q p p' ps ps' r x@
  cLet :: Bool -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a
    -> AnnArray (RsrcAnn a) -> AnnArray (RsrcAnn a) -> RsrcAnn a -> Id -> [Constraint],
  -- | @ 'cWeakenVar' q r @
  cWeakenVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cWeaken' q q' p p'@
  cWeaken :: [RuleArg] -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cOptimize' q q' @ returns constraints that minimize \[\Phi(\Gamma\mid Q) - \Phi(\Gamma\mid Q')\]
  cOptimize :: RsrcAnn a -> RsrcAnn a -> OptiMonad Target}
  

type GroundPot = Potential CoeffsMap
type CombPot = Potential [CoeffsMap]
