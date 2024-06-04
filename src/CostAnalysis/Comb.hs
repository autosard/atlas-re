module CostAnalysis.Comb where

import qualified CostAnalysis.Potential as P 
import CostAnalysis.Potential(Potential(Potential),
                              Constraint,
                              GroundPot,
                              CombPot,
                              IndexedCoeffs,
                              AnnArray)

import Data.List(zipWith5, zipWith4, zipWith7, intercalate)
import Data.Text (Text)

rsrcAnn :: [GroundPot] -> Int -> Text -> Int -> [IndexedCoeffs]
rsrcAnn pots id label len = map (\p -> P.rsrcAnn p id label len) pots

--forAll :: [GroundPot] -> [IndexedCoeffs] -> [IndexedCoeffs]
--  -> [Int] -> Bool -> AnnArray [IndexedCoeffs]
--forAll pots ps rs ids = zipWith3 

annLen :: [GroundPot] -> [IndexedCoeffs] -> Int
annLen (pot:_) (coeffs:_) = P.annLen pot coeffs

concatZipWith3 :: (a -> b -> c -> [d]) -> [a] -> [b] -> [c] -> [d]
concatZipWith3 f a b c = concat $ zipWith3 f a b c

cLeaf = concatZipWith3 P.cLeaf
cNode = concatZipWith3 P.cNode
cPair = concatZipWith3 P.cPair

concatZipWith4 :: (a -> b -> c -> d -> [f]) -> [a] -> [b] -> [c] -> [d] -> [f]
concatZipWith4 f a b c d = concat $ zipWith4 f a b c d

cMatch :: [GroundPot]
  -> [IndexedCoeffs] -> [IndexedCoeffs] -> [IndexedCoeffs]
  -> [Constraint]
cMatch = concatZipWith4 P.cMatch

concatZipWith5 :: (a -> b -> c -> d -> e -> [f]) -> [a] -> [b] -> [c] -> [d] -> [e] -> [f]
concatZipWith5 f a b c d e = concat $ zipWith5 f a b c d e

cLetBase :: [GroundPot]
  -> [IndexedCoeffs] -> [IndexedCoeffs] -> [IndexedCoeffs] -> [IndexedCoeffs]
  -> [Constraint]
cLetBase = concatZipWith5 P.cLetBase

concatZipWith7 :: (a -> b -> c -> d -> e -> f -> g -> [h]) -> [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [g] -> [h]
concatZipWith7 f l1 l2 l3 l4 l5 l6 l7 = concat $ zipWith7 f l1 l2 l3 l4 l5 l6 l7

cLet :: [GroundPot] -> Bool
  -> [IndexedCoeffs] -> [IndexedCoeffs] -> [IndexedCoeffs]
  -> AnnArray [IndexedCoeffs] -> AnnArray [IndexedCoeffs]
  -> [IndexedCoeffs] -> [Constraint]
cLet pots neg = concatZipWith7 (`P.cLet` neg) pots 

printPot :: [GroundPot] -> [IndexedCoeffs] -> String
printPot pots coeffs = intercalate " + " $ zipWith P.printPot pots coeffs
  
-- combPot :: [GroundPot] -> CombPot
-- combPot pots = Potential
--   (rsrcAnn pots)
--   (annLen pots)
--   (cLeaf pots)
--   (cNode pots)
--   (cPair pots)
--   (cMatch pots)
--   (cLetBase pots)
--   (cLet pots)
--   (printPot pots)
