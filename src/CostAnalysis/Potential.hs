{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}

module CostAnalysis.Potential where
import Data.Text(Text, unpack)
import Data.List(intercalate)
import Data.Map(Map)
import qualified Data.Map as M

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

data Constraint = Eq Coeff Coeff
  | EqSum Coeff [Coeff]
  | EqPlusConst Coeff Coeff Rational
  | EqMinusConst Coeff Coeff Rational
  | Zero Coeff
  | NotZero Coeff
  | Le Coeff Coeff
  | GeSum [Coeff] Coeff
  | Impl Constraint Constraint
  deriving (Eq, Show)



data Potential a = Potential {
  rsrcAnn :: Int -> Text -> Int -> a,
  enumAnn :: a -> Bool -> [[Int]],
  forAllIdx :: [[Int]] -> [Int] -> a -> AnnArray a,
  elems :: AnnArray a -> [a],
  annLen :: a -> Int,
  cPlusConst :: a -> Rational -> a -> [Constraint],
  cMinusConst :: a -> Rational -> a -> [Constraint],
  cLeaf :: a -> a -> [Constraint],
  cNode :: a -> a -> [Constraint],
  cPair :: a -> a -> [Constraint],
  cMatch :: a -> a -> a -> [Constraint],
  cLetBase :: a -> a -> a -> a -> [Constraint],
  cLet :: Bool -> a -> a -> a -> AnnArray a -> AnnArray a -> a -> [Constraint],
  printPot :: a -> String}

type GroundPot = Potential IndexedCoeffs
type CombPot = Potential [IndexedCoeffs]
