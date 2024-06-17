{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}

module CostAnalysis.Potential where
import Data.Text(Text, unpack)
import Data.List(intercalate)
import Data.Map(Map)
import qualified Data.Map as M
import CostAnalysis.Rules ( RuleArg )

data Coeff
  = Unknown Int Text Text [Int]
  | Known Int Text Text [Int] Rational
  deriving (Eq, Show)

printCoeff :: Coeff -> String
printCoeff (Unknown id label kind idx) =
  unpack label ++ "_" ++ show id ++ "_" ++ unpack kind ++ "_" ++ printIdx idx
printCoeff (Known _ _ _ _ v) = show v



printIdx :: [Int] -> String
printIdx idx = "(" ++ intercalate "," (map show idx) ++ ")" 

data IndexedCoeffs = IndexedCoeffs Int (Map [Int] Coeff)
  deriving (Show)

infixl 9 !
(!) :: IndexedCoeffs -> [Int] -> Coeff
(!) (IndexedCoeffs _ m) k = case M.lookup k m of
  Just c -> c
  Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation '" ++ show m ++ "'."

type family AnnArray a

type instance AnnArray IndexedCoeffs = Map [Int] IndexedCoeffs
type instance AnnArray [IndexedCoeffs] = [Map [Int] IndexedCoeffs]

infixl 9 !!
(!!) :: AnnArray IndexedCoeffs -> [Int] -> IndexedCoeffs
(!!) m k = case M.lookup k m of
  Just c -> c
  Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation list."


data Constraint =
  -- | 'Eq' q p = \[q = p\]
  Eq Coeff Coeff 
  -- | 'EqSum' q ps = \[q = \sum^N_{i=1} p_i \]
  | EqSum Coeff [Coeff]
  -- | 'EqPlusConst' q p = \[q = p + c \]
  | EqPlusConst Coeff Coeff Rational
  -- | 'EqMinusConst' q p = \[q = p - c \]
  | EqMinusConst Coeff Coeff Rational
  -- | 'EqMinusVar' q p = \[q = p - k \]
  | EqMinusVar Coeff Coeff
  -- | 'EqPlusMulti' q p r = \[ q = p \cdot k r\]
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
  deriving (Eq, Show)

data FunRsrcAnn a = FunRsrcAnn {
  withCost :: (a, a),
  withoutCost :: (a, a)}
  deriving(Show)

data Potential a = Potential {
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label len@ constructs a fresh resource annotation of length @len@. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> Int -> a,
  -- | @ 'enumAnn' len neg @ enumerates coefficient indicies of length @len@. If neg is @True@, allow negative values for the annotation constant. 
  enumAnn :: Int -> Bool -> [[Int]],
  -- | @ 'forAllIdx' idxs ids q@ constructs a fresh annotation of length @len@ for every index from @idxs@ using @ids@ as identifiers. 
  forAllIdx :: [[Int]] -> [Int] -> Int -> AnnArray a,
  -- | @ 'elems' a@ converts an annotation array to a list.
  elems :: AnnArray a -> [a],
  -- | @ 'annLen' q' @ returns the length (number of tree arguments) of the annotation @q@. 
  annLen :: a -> Int,
  
  -- Constraint generation
  
  -- | @ 'cPlusConst' q c p@, returns constraints that guarantee \[\phi(*\mid P) = \phi(*\mid Q) + C\] where @c@ is constant.
  cPlusConst :: a -> a -> Rational -> [Constraint],
  -- | @ 'cMinusConst' q c p@, returns constraints that guarantee \[\phi(*\mid P) = \phi(*\mid Q) - C\] where @c@ is constant.
  cMinusConst :: a -> a -> Rational -> [Constraint],
  -- | @ 'cMinusVar' q p@, returns constraints that guarantee \[\phi(*\mid P) = \phi(*\mid Q) - K\] where @k@ is a fresh variable.
  cMinusVar :: a -> a -> [Constraint],
  -- | @ 'cPlusMulti' q p r@, returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid Q) - K\] where @k@ is a fresh variable.
  cPlusMulti :: a -> a -> a -> [Constraint],
  -- | @ 'cLeaf' q q'@, returns constraints that guarantee \[\phi(\varnothing\mid Q) = \phi(\verb|leaf| \mid Q')\]  
  cLeaf :: a -> a -> [Constraint],
  -- | @ 'cNode' q q'@, returns constraints that guarantee \[\forall u: T,b: B, v:T .\,\phi(u,v\mid Q) = \phi(\verb|node| \,u\, b\, v\mid Q')\]
  cNode :: a -> a -> [Constraint],
  -- | @ 'cPair' q q'@, returns constraints that guarantee \[\forall u: T, v:B .\,\phi(u,v\mid Q) = \phi((u, v) \mid Q')\]
  cPair :: a -> a -> [Constraint],
  -- | @ 'cMatchLeaf' q q'@, returns constraints that guarantee \[\forall  \Gamma.\ \phi(\Gamma, \verb|leaf| \mid Q) = \phi(\Gamma, \mid Q')\]
  cMatchLeaf :: a -> a -> [Constraint],
  -- | @ 'cMatchNode' q q'@, returns constraints that guarantee \[\forall  \Gamma,u: T, b: B, v. T.\ \phi(\Gamma, \verb|node|\,u\,b\,v \mid Q) = \phi(\Gamma, u, b, v\mid Q')\]
  cMatchNode :: a -> a -> [Constraint],
  -- | @ 'cLetBase' q p r p'@
  cLetBase :: a -> a -> a -> a -> [Constraint],
  -- | @ 'cLet' q p p' ps ps' r@
  cLet :: Bool -> a -> a -> a -> AnnArray a -> AnnArray a -> a -> [Constraint],
  -- | @ 'cWeaken' q q' p p'@
  cWeaken :: [RuleArg] -> a -> a -> a -> a -> [Constraint],
  -- | @ 'printPot' q@, prints the potential function represented by @q@.
  printPot :: a -> String}

type GroundPot = Potential IndexedCoeffs
type CombPot = Potential [IndexedCoeffs]
