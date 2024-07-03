{-# LANGUAGE StrictData #-}

module CostAnalysis.Potential where
import Data.Text(Text)
import Primitive(Id)

import CostAnalysis.Rules ( RuleArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization (OptiMonad, Target)
import CostAnalysis.RsrcAnn


data Potential a = Potential {
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label vars@ constructs a fresh resource annotation with tree arguments from @vars@. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> [Id] -> RsrcAnn a,
  
  -- | @ 'forAllIdx' neg xs x id label ys@ for all combinations of variables in @xs@ with the var @x@, construct a fresh annotation starting with id @id@ and with vars in @ys@. @neg@ allows negative constants. Returns the last used id + 1. 
  forAllCombinations :: Bool -> [Id] -> Id -> Int -> Text -> [Id] -> (AnnArray (RsrcAnn a), Int),
  
  -- | @ 'elems' a@ converts an annotation array to a list.
  elems :: AnnArray (RsrcAnn a) -> [RsrcAnn a],

  
  -- Constraint generation
  
  -- | @ 'cPlusConst' q p c@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + C\] where @c@ is constant.
  cPlusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusConst' q c p@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - C\] where @c@ is constant.
  cMinusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusVar' q p@ returns constraints that guarantee \[\phi(*\mid P) = \phi(*\mid Q) - K\] where @k@ is RsrcAnn a fresh variable.
  cMinusVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cPlusMulti' q p r@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\] where @k@ is a fresh variable.
  cPlusMulti :: RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cLeaf' q q'@ returns constraints that guarantee \[\phi(\varnothing\mid Q) = \phi(\verb|leaf| \mid Q')\]  
  cLeaf :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cNode' q q'@ returns constraints that guarantee \[\forall u: T,b: B, v:T .\,\phi(u,v\mid Q) = \phi(\verb|node| \,u\, b\, v\mid Q')\]
  cNode :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cPair' q q'@, returns constraints that guarantee \[\forall u: T, v:B .\,\phi(u,v\mid Q) = \phi((u, v) \mid Q')\]
  cPair :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cMatchLeaf' q q' t@ returns constraints that guarantee \[\forall  \Gamma.\ \phi(\Gamma, \verb|leaf| \mid Q) = \phi(\Gamma, \mid Q')\] where @t@ is the variable that matched.
  cMatchLeaf :: RsrcAnn a -> RsrcAnn a -> Id -> [Constraint],
  -- | @ 'cMatchNode' q q' t u v@ returns constraints that guarantee \[\forall  \Gamma,u: T, b: B, v. T.\ \phi(\Gamma, \verb|node|\,u\,b\,v \mid Q) = \phi(\Gamma, u, b, v\mid Q')\] where @t@ is the variable that matched.
  cMatchNode :: RsrcAnn a -> RsrcAnn a -> Id -> Id -> Id -> [Constraint],
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
