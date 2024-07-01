{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module CostAnalysis.Potential where
import Data.Text(Text, unpack)
import Data.Map(Map)
import Data.Set(Set)
import qualified Data.Set as S
import Primitive(Id)
import qualified Data.Map as M
import CostAnalysis.Rules ( RuleArg )
import CostAnalysis.Solving
import CostAnalysis.Coeff


data RsrcAnn a = RsrcAnn {
  -- | Number of tree arguments
  --len :: Int,
  -- | Tree args
  args :: [Id],
  -- | Map of variables to coefficients
  coeffs :: a}
  deriving (Eq, Show)

type GroundAnn = RsrcAnn CoeffsMap
type CombinedAnn = RsrcAnn [CoeffsMap]

class Index a where
  infixl 9 !
  (!) :: GroundAnn -> a -> Coeff

instance Index Id where
  (!) ann@(RsrcAnn _ coeffs) x = case M.lookup (Pure x) coeffs of
    Just c -> c
    Nothing -> error $ "Invalid index '" ++ unpack x ++ "' for annotation '" ++ show ann ++ "'."

instance Index [Factor] where
  (!) :: GroundAnn -> [Factor] -> Coeff
  (!) ann factors = ann!S.fromList factors

factorGTZero :: Factor -> Bool
factorGTZero (Arg _ a) = a > 0
factorGTZero (Const c) = c > 0

instance Index (Set Factor) where
  (!) :: GroundAnn -> Set Factor -> Coeff
  (!) ann@(RsrcAnn _ coeffs) factors =
    let factors' = S.filter factorGTZero factors in
      case M.lookup (Mixed factors') coeffs of
        Just c -> c
        Nothing -> error $ "Invalid index '" ++ show factors ++ "' for annotation '" ++ show ann ++ "'."

type family AnnArray a


type instance AnnArray GroundAnn = Map (Set Factor) GroundAnn
type instance AnnArray CombinedAnn = [Map (Set Factor) GroundAnn]

infixl 9 !!
(!!) :: AnnArray GroundAnn -> Set Factor -> GroundAnn
(!!) arr k = let k' = S.filter factorGTZero k in
    case M.lookup k' arr of
      Just c -> c
      Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation array."


data FunRsrcAnn a = FunRsrcAnn {
  withCost :: (RsrcAnn a, RsrcAnn a),
  withoutCost :: (RsrcAnn a, RsrcAnn a)}
  deriving(Show)

data Potential a = Potential {
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label vars@ constructs a fresh resource annotation with tree arguments from @vars@. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> [Id] -> RsrcAnn a,
  
  -- | @ 'forAllIdx' neg xs x id label ys@ for all combinations of variables in @xs@ with the var @x@, construct a fresh annotation starting with id @id@ and with vars in @ys@. @neg@ allows negative constants. Returns the last used id + 1. 
  forAllCombinations :: Bool -> [Id] -> Id -> Int -> Text -> [Id] -> (AnnArray (RsrcAnn a), Int),
  
  -- | @ 'elems' a@ converts an annotation array to a list.
  elems :: AnnArray (RsrcAnn a) -> [RsrcAnn a],

  
  -- Constraint generation
  
  -- | @ 'cPlusConst' q p c@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + C\] where @c@ is constant.
  cPlusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusConst' q c p@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - C\] where @c@ is constant.
  cMinusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusVar' q p@, returns constraints that guarantee \[\phi(*\mid P) = \phi(*\mid Q) - K\] where @k@ is RsrcAnn a fresh variable.
  cMinusVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cPlusMulti' q p r@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\] where @k@ is a fresh variable.
  cPlusMulti :: RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cLeaf' q q'@, returns constraints that guarantee \[\phi(\varnothing\mid Q) = \phi(\verb|leaf| \mid Q')\]  
  cLeaf :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cNode' q q'@, returns constraints that guarantee \[\forall u: T,b: B, v:T .\,\phi(u,v\mid Q) = \phi(\verb|node| \,u\, b\, v\mid Q')\]
  cNode :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cPair' q q'@, returns constraints that guarantee \[\forall u: T, v:B .\,\phi(u,v\mid Q) = \phi((u, v) \mid Q')\]
  cPair :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cMatchLeaf' q q' t@, returns constraints that guarantee \[\forall  \Gamma.\ \phi(\Gamma, \verb|leaf| \mid Q) = \phi(\Gamma, \mid Q')\] where @t@ is the variable that matched.
  cMatchLeaf :: RsrcAnn a -> RsrcAnn a -> Id -> [Constraint],
  -- | @ 'cMatchNode' q q' t u v@, returns constraints that guarantee \[\forall  \Gamma,u: T, b: B, v. T.\ \phi(\Gamma, \verb|node|\,u\,b\,v \mid Q) = \phi(\Gamma, u, b, v\mid Q')\] where @t@ is the variable that matched.
  cMatchNode :: RsrcAnn a -> RsrcAnn a -> Id -> Id -> Id -> [Constraint],
  -- | @ 'cLetBase' q p r p'@
  cLetBase :: RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cLet' q p p' ps ps' r x@
  cLet :: Bool -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a
    -> AnnArray (RsrcAnn a) -> AnnArray (RsrcAnn a) -> RsrcAnn a -> Id -> [Constraint],
  -- | @ 'cWeakenVar' q r @
  cWeakenVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cWeaken' q q' p p'@
  cWeaken :: [RuleArg] -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint]}
  -- | @ 'printPot' q@, prints the potential function represented by @q@.
  -- printPot :: RsrcAnn a -> String}

type GroundPot = Potential CoeffsMap
type CombPot = Potential [CoeffsMap]
