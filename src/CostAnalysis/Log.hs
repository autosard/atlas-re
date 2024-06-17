{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module CostAnalysis.Log where

import qualified Data.Map as M
import Data.List(delete, intercalate)
import Prelude hiding ((!!))
import Data.Text(Text)

import CostAnalysis.Potential(IndexedCoeffs(IndexedCoeffs),
                              Constraint(..),
                              Coeff(Unknown), (!),
                              (!!),
                              AnnArray, printCoeff, GroundPot, Potential (Potential))
import qualified Data.Text as T
import CostAnalysis.Rules (RuleArg)

aRange = [1, 0]
bRange = [0, 2]
dRange = aRange
eRange = bRange
eRangeNeg = -1 : eRange
  
abIdx :: Int -> [[Int]]
abIdx 0 = [[x] | x <- bRange]
abIdx n = [x:y | x <- aRange, y <- abIdx (n-1)]

aIdx :: Int -> [[Int]]
aIdx 1 = [[x] | x <- aRange]
aIdx n = [x:y | x <- aRange, y <- aIdx (n-1)]

rsrcAnn :: Int -> Text -> Int -> IndexedCoeffs
rsrcAnn id label len = IndexedCoeffs len $ M.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [([x], Unknown id label "log" [x]) | x <- [1..len]]
        logCoeffs = map (\idx -> (idx, Unknown id label "log" idx)) $ abIdx len

enumAnn :: Int -> Bool -> [[Int]]
enumAnn len neg = let k = len - 1
                      _eRange = if neg then eRangeNeg else eRange in
  [bs ++ [d,e] | 
    bs <- delete (replicate k 0) (aIdx k),
    d <- delete 0 dRange,
    e <- _eRange]

forAllIdx :: [[Int]] -> [Int] -> Int -> AnnArray IndexedCoeffs
forAllIdx idxs ids len = M.fromList $ zipWith go idxs ids
  where go idx id = (idx, rsrcAnn id (T.concat ["P_", T.pack $ show idx]) len)

elems :: AnnArray IndexedCoeffs -> [IndexedCoeffs]
elems = M.elems
  
annLen :: IndexedCoeffs -> Int
annLen (IndexedCoeffs len _ ) = len

-- P = Q + c
cPlusConst :: IndexedCoeffs -> Rational -> IndexedCoeffs -> [Constraint]
cPlusConst q c p = let m = annLen q in
  EqPlusConst (p!(replicate m 0 ++ [2])) (q!(replicate m 0 ++ [2])) c :
  [Eq (q![i]) (p![i]) | i <- [1..m]]
  ++ [Eq (q!(as ++ [b])) (p!(as ++ [b])) |
      as <- delete (replicate m 0) (aIdx m), b <- bRange]

-- P = Q - c
cMinusConst :: IndexedCoeffs -> Rational -> IndexedCoeffs -> [Constraint]
cMinusConst q c p = let m = annLen q in
  EqMinusConst (p!(replicate m 0 ++ [2])) (q!(replicate m 0 ++ [2])) c :
  [Eq (q![i]) (p![i]) | i <- [1..m]]
  ++ [Eq (q!(as ++ [b])) (p!(as ++ [b])) |
      as <- delete (replicate m 0) (aIdx m), b <- bRange]

cMinusVar :: IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cMinusVar q p = let m = annLen q in
  EqMinusVar (p!(replicate m 0 ++ [2])) (q!(replicate m 0 ++ [2])):
  [Eq (q![i]) (p![i]) | i <- [1..m]]
  ++ [Eq (q!(as ++ [b])) (p!(as ++ [b])) |
      as <- delete (replicate m 0) (aIdx m), b <- bRange]


cLeaf :: IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cLeaf q q' =
  EqSum (q![2]) [q'![1], q![0,2]] :
  [EqSum (q![c]) [q'![a,b] | a <- aRange, b <- bRange, a + b == c] | c <- bRange, c > 2]

cNode :: IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cNode q q' =
  Eq (q![1]) (q'![1]) :
  Eq (q![2]) (q'![1]) :
  Eq (q![1,0,0]) (q'![1]) :
  Eq (q![0,1,0]) (q'![1]) :
  [Eq (q![a,a,c]) (q'![a,c]) | a <- aRange, c <- bRange]

cPair :: IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cPair q q' =
  Eq (q![1]) (q'![1]) :
  [Eq (q![a,c]) (q'![a,c]) | a <- aRange, c <- bRange]

cMatchLeaf :: IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cMatchLeaf q p = let m = annLen q - 1 in
  [Eq (q![i]) (p![i]) | i <- [1..m]]
  ++ [EqSum (p!(as ++ [c])) [q!(as ++ [a,b])
                            | a <- aRange, b <- bRange, a + b == c]
     | as <- aIdx m, c <- bRange]

cMatchNode :: IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cMatchNode q r = let m = annLen q - 1 in
  Eq (r![m+1]) (q![m+1]) :
  Eq (r![m+2]) (q![m+1]) :
  Eq (r!(replicate m 0 ++ [1,0,0])) (q![m+1]) :
  Eq (r!(replicate m 0 ++ [0,1,0])) (q![m+1]) :
  [Eq (r!(as ++ [a,a,b])) (q!(as ++ [a,b]))
  | as <- aIdx m, a <- aRange, b <- bRange]
  ++ [Eq (q![i]) (r![i]) | i <- [1..m]]
  
-- cMatch :: IndexedCoeffs -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
-- cMatch q p r = let m = annLen q - 1 in
--   Eq (r![m+1]) (q![m+1]) :
--   Eq (r![m+2]) (q![m+1]) :
--   Eq (r!(replicate m 0 ++ [1,0,0])) (q![m+1]) :
--   Eq (r!(replicate m 0 ++ [0,1,0])) (q![m+1]) :
--   [Eq (r!(as ++ [a,a,b])) (q!(as ++ [a,b]))
--   | as <- aIdx m, a <- aRange, b <- bRange]
--   ++ [Eq (q![i]) (r![i]) | i <- [1..m]]
--   ++ [EqSum (p!(as ++ [c])) [q!(as ++ [a,b])
--                             | a <- aRange, b <- bRange, a + b == c]
--      | as <- aIdx m, c <- bRange]

cLetBase :: IndexedCoeffs -> IndexedCoeffs -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cLetBase q p r p' = let m = annLen p
                        k = annLen r in
  [Eq (r!(replicate 0 k ++ [c])) (p'![c]) | c <- bRange]
  ++ [Eq (r![j]) (q![m+j]) | j <- [1..k]] 
  ++ [Eq (p![i]) (q![i]) | i <- [1..m]]
  ++ [Eq (p!(as ++ [c])) (q!(as ++ replicate k 0 ++ [c]))
     | as <- aIdx m, c <- bRange]
  ++ [Eq (q!(replicate m 0 ++ bs ++ [c])) (r!(bs ++ [c]))
     | bs <- delete (replicate k 0) (aIdx k), c <- bRange]

cLet :: Bool -> IndexedCoeffs -> IndexedCoeffs
  -> IndexedCoeffs -> AnnArray IndexedCoeffs
  -> AnnArray IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cLet neg q p p' ps ps' r = let m = annLen p
                               k = annLen r - 1
                               _eRange = if neg then eRangeNeg else eRange in
  Eq (r![k+1]) (p'![1]) :
  [Eq (p![i]) (q![i]) | i <- [1..m]]
  ++ [Eq (p!(as ++ [c])) (q!(as ++ replicate k 0 ++ [c]))
     | as <- aIdx m, c <- bRange]
  ++ [Eq (r![j]) (q![m+j]) | j <- [1..k]]
  ++ [Eq (r!(replicate 0 k ++ [d,e])) (p'![d,e])
     | d <- aRange, e <- bRange]
  ++ [Eq (r!(bs ++ [0,c])) (q!(replicate 0 m ++ bs ++ [c]))
     | bs <- delete (replicate k 0) (aIdx k), c <- bRange]
  ++ [EqSum (q!(as ++ bs ++ [c])) [(ps!!(bs ++ [d,e]))!(as ++ [c + max (-e) 0])
                                  | d <- delete 0 dRange,
                                    e <- _eRange]
     | bs <- delete (replicate k 0) (aIdx k),
       as <- delete (replicate m 0) (aIdx m),
       c <- bRange]
  ++ [Eq (r!(bs ++ [d,e])) (ps'!!(bs ++ [d,e])![d, max e 0])
     | bs <- delete (replicate k 0) (aIdx k),
       d <- delete 0 dRange,
       e <- _eRange]
  ++ [Zero (ps'!!(bs ++ [d,e])![d',e'])
      | bs <- delete (replicate k 0) (aIdx k),
      d <- delete 0 dRange,
      e <- _eRange,
      d' <- delete 0 dRange,
      d' /= d,
      e' <- _eRange,
      e' /= max e 0]
  ++ [GeSum [ps!!(bs ++ [d,e])!(as ++ [c])
            | as <- aIdx m, c <- bRange]
       (ps'!!(bs ++ [d,e])![d, max e 0])
     | bs <- delete (replicate k 0) (aIdx k),
       d <- delete 0 dRange,
       e <- _eRange]
  ++ [Impl (Zero (ps!!(bs ++ [d,e])!(as ++ [c])))
      (Le (ps'!!(bs ++ [d,e])![d, max e 0]) (ps!!(bs ++ [d,e])!(as ++ [c])))
     | bs <- delete (replicate k 0) (aIdx k),
     d <- delete 0 dRange,
     e <- _eRange,
     as <- delete (replicate m 0) (aIdx m),
     c <- bRange]

cWeaken :: [RuleArg] -> IndexedCoeffs -> IndexedCoeffs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cWeaken args q q' p p' = []

-- TODO accept arguments to be printed as well. 
printPot :: IndexedCoeffs -> String
printPot qs@(IndexedCoeffs len _) = rankCoeffs ++ " " ++ logCoeffs 
  where rankCoeffs = intercalate " + " [_printCoeff (qs![x]) ++ "rk(t)" | x <- [1..len]]
        logCoeffs = intercalate " + " $ map (\idx -> _printCoeff (qs!idx) ++ printLog idx) (abIdx len)
        _printCoeff q = case printCoeff q of
          "0" -> ""
          s -> s
        printLog :: [Int] -> String
        printLog xs = "log(" ++ intercalate " + " (map show xs) ++ ")"

logPot :: GroundPot
logPot = Potential
  rsrcAnn
  enumAnn
  forAllIdx
  elems
  annLen
  cPlusConst
  cMinusConst
  cMinusVar
  cLeaf
  cNode
  cPair
  cMatchLeaf
  cMatchNode
  cLetBase
  cLet
  cWeaken
  printPot
