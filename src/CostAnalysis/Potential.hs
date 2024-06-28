{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module CostAnalysis.Potential where
import Data.Text(Text, unpack)
import Data.List(intercalate)
import Data.Map(Map)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.List(intercalate)
import Primitive(Id)
import qualified Data.Map as M
import CostAnalysis.Rules ( RuleArg )


data Coeff
  = Unknown Int Text Text CoeffIdx
  | Known Int Text Text CoeffIdx Rational
  deriving (Eq, Ord, Show)

printCoeff :: Coeff -> String
-- printCoeff (Unknown id label kind) =
--   unpack label ++ "_" ++ show id ++ "_" ++ unpack kind ++ "_" 
printCoeff (Known _ _ _ _ v) = show v

-- printIdx :: [Int] -> String
-- printIdx idx = "(" ++ intercalate "," (map show idx) ++ ")" 

data Factor = Const Int | Arg Id Int
  deriving (Eq, Ord)

instance Show Factor where
  show (Const c) = show c
  show (Arg x a) = T.unpack x ++ "^" ++ show a

infixl 9 ^
(^) :: Id -> Int -> Factor
(^) = Arg

data CoeffIdx = Pure Id | Mixed (Set Factor)
  deriving (Eq, Ord)

instance Show CoeffIdx where
  show (Pure x) = "(" ++ T.unpack x ++ ")"
  show (Mixed xs) = "(" ++ intercalate "," (map show (S.toDescList xs)) ++ ")"

type CoeffsMap = Map CoeffIdx Coeff


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

data Constraint =
  -- | 'Eq' q p = \[q = p\]
  Eq Coeff Coeff 
  -- | 'EqSum' q ps = \[q = \sum^N_{i=1} p_i \]
  | EqSum Coeff [Coeff]
  -- | 'EqPlusConst' q p c = \[q = p + c \]
  | EqPlusConst Coeff Coeff Rational
  -- | 'EqMinusConst' q p c = \[q = p - c \]
  | EqMinusConst Coeff Coeff Rational
  -- | 'EqMinusVar' q p = \[q = p - k \]
  | EqMinusVar Coeff Coeff
  -- | 'EqPlusMulti' q p r = \[ q = p + k r\]
  | EqPlusMulti Coeff Coeff Coeff
  -- | 'Zero' q = \[q = 0 \]
  | Zero Coeff
  -- | 'NotZero' q = \[q \neq 0 \]
  | NotZero Coeff
  -- | 'Le' q p = \[q < p \]
  | Le Coeff Coeff
  -- | 'GeSum' q ps = \[q \geq \sum^N_{i=1} p_i \]
  | GeSum [Coeff] Coeff
  -- | 'GeSum' c1 c2 = \[C_1 \Rightarrow C_2 \]
  | Impl Constraint Constraint
  deriving (Eq, Ord, Show)

data FunRsrcAnn a = FunRsrcAnn {
  withCost :: (RsrcAnn a, RsrcAnn a),
  withoutCost :: (RsrcAnn a, RsrcAnn a)}
  deriving(Show)

data Potential a = Potential {
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label vars@ constructs a fresh resource annotation with tree arguments from @vars@. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> [Id] -> RsrcAnn a,
  
  -- | @ 'forAllIdx' neg xs x id label ys@ for all combinations of variables in @xs@ with the var @x@, construct a fresh annotation starting with id @id@ and with vars in @ys@. @neg@ allows negative constants. Returns the last used id + 1. 
  forAllCombinations :: Bool -> [Id] -> Id -> Int -> Text -> [Id] -> (AnnArray a, Int),
  
  -- | @ 'elems' a@ converts an annotation array to a list.
  elems :: AnnArray a -> [RsrcAnn a],

  
  -- Constraint generation
  
  -- | @ 'cPlusConst' q p c@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + C\] where @c@ is constant.
  cPlusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusConst' q c p@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - C\] where @c@ is constant.
  cMinusConst :: RsrcAnn a -> RsrcAnn a -> Rational -> [Constraint],
  -- | @ 'cMinusVar' q p@, returns constraints that guarantee \[\phi(*\mid P) = \phi(*\mid Q) - K\] where @k@ is RsrcAnn a fresh variable.
  cMinusVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cPlusMulti' q p r@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\] where @k@ is RsrcAnn a fresh variable.
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
    -> AnnArray a -> AnnArray a -> RsrcAnn a -> Id -> [Constraint],
  -- | @ 'cWeakenVar' q r @
  cWeakenVar :: RsrcAnn a -> RsrcAnn a -> [Constraint],
  -- | @ 'cWeaken' q q' p p'@
  cWeaken :: [RuleArg] -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> RsrcAnn a -> [Constraint]}
  -- | @ 'printPot' q@, prints the potential function represented by @q@.
  -- printPot :: RsrcAnn a -> String}

type GroundPot = Potential GroundAnn 
type CombPot = Potential CombinedAnn
