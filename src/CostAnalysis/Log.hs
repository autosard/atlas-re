{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module CostAnalysis.Log where

import qualified Data.Map as M
import Data.List(delete, intercalate)
import Prelude hiding ((!!))
import Data.Text(Text)
import Control.Monad.Reader

import CostAnalysis.Potential(IndexedCoeffs(IndexedCoeffs),
                              Constraint(..),
                              Coeff(Unknown), (!),
                              (!!),
                              AnnArray, printCoeff, GroundPot, Potential (Potential))
import qualified Data.Text as T
import CostAnalysis.Rules (RuleArg)

data LogPotArgs = LogPotArgs {
  aRange :: ![Int],
  bRange :: ![Int],
  dRange :: ![Int],
  eRange :: ![Int],
  eRangeNeg :: ![Int]}

--aRange = [1, 0]
--bRange = [0, 2]
--dRange = aRange
--eRange = bRange
--eRangeNeg = -1 : eRange
  
abIdx :: LogPotArgs
  -> Int -> [[Int]]
abIdx args 0 = [[x] | x <- bRange args]
abIdx args n = [x:y | x <- aRange args, y <- abIdx args (n-1)]

aIdx :: LogPotArgs
  -> Int -> [[Int]]
aIdx args 1 = [[x] | x <- aRange args]
aIdx args n
  | n <= 0 = [[]]
  | otherwise = [x:y | x <- aRange args, y <- aIdx args (n-1)]

rsrcAnn :: LogPotArgs
  -> Int -> Text -> Int -> IndexedCoeffs
rsrcAnn args id label len = IndexedCoeffs len $ M.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [([x], Unknown id label "log" [x]) | x <- [1..len]]
        logCoeffs = map (\idx -> (idx, Unknown id label "log" idx)) $ abIdx args len

enumAnn :: LogPotArgs
  -> Int -> Bool -> [[Int]]
enumAnn args len neg = let k = len - 1
                           _eRange = if neg then eRangeNeg args else eRange args in
  [bs ++ [d,e] | 
    bs <- aIdx args k,
    bs /= replicate k 0,
    d <- dRange args,
    d /= 0,
    e <- _eRange]

forAllIdx :: LogPotArgs
  -> [[Int]] -> [Int] -> Int -> Text -> AnnArray IndexedCoeffs
forAllIdx args idxs ids len label = M.fromList $ zipWith go idxs ids
  where go idx id = (idx, rsrcAnn args id (T.concat [label, "_", T.pack $ show idx]) len)

elems :: AnnArray IndexedCoeffs -> [IndexedCoeffs]
elems = M.elems
  
annLen :: IndexedCoeffs -> Int
annLen (IndexedCoeffs len _ ) = len

eqExceptConst :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
eqExceptConst args q p = let m = annLen q in
  [Eq (q![i]) (p![i]) | i <- [1..m]]
  ++ [Eq (q!idx) (p!idx)
     | let idxs = [as ++ [b]
                  | as <- aIdx args m, b <- bRange args],
       idx <- idxs, idx /= replicate m 0 ++ [2]]
       
-- P = Q + c
cPlusConst :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> Rational -> [Constraint]
cPlusConst args q p c = let m = annLen q in
  EqPlusConst (q!(replicate m 0 ++ [2])) (p!(replicate m 0 ++ [2])) c :
  eqExceptConst args q p

-- P = Q - c
cMinusConst :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> Rational -> [Constraint]
cMinusConst args q p c  = let m = annLen q in
  EqMinusConst (q!(replicate m 0 ++ [2])) (p!(replicate m 0 ++ [2])) c :
  eqExceptConst args q p

cMinusVar :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cMinusVar args q p = let m = annLen q in
  EqMinusVar (q!(replicate m 0 ++ [2])) (p!(replicate m 0 ++ [2])):
  eqExceptConst args q p
  
cPlusMulti :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cPlusMulti args q p r = let m = annLen q in
  [EqPlusMulti (q![i]) (p![i]) (r![i]) | i <- [1..m]]
  ++ [EqPlusMulti (q!(as ++ [b])) (p!(as ++ [b])) (r!(as ++ [b]))
     | as <- aIdx args m, b <- bRange args]

cLeaf :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cLeaf args q q' =
  EqSum (q![2]) [q'![1], q'![0,2]] :
  [EqSum (q![c]) [q'![a,b]
                 | a <- aRange args,
                   b <- bRange args, a + b == c]
  | c <- bRange args, c > 2]

cNode :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cNode args q q' =
  Eq (q![1]) (q'![1]) :
  Eq (q![2]) (q'![1]) :
  Eq (q![1,0,0]) (q'![1]) :
  Eq (q![0,1,0]) (q'![1]) :
  [Eq (q![a,a,c]) (q'![a,c])
  | a <- aRange args,
    c <- bRange args]

cPair :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cPair args q q' =
  Eq (q![1]) (q'![1]) :
  [Eq (q![a,c]) (q'![a,c])
  | a <- aRange args,
    c <- bRange args]

cMatchLeaf :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cMatchLeaf args q p = let m = annLen q - 1 in
  [Eq (q![i]) (p![i]) | i <- [1..m]]
  ++ [EqSum (p!(as ++ [c])) [q!(as ++ [a,b])
                            | a <- aRange args,
                              b <- bRange args,
                              a + b == c]
     | as <- aIdx args m,
       c <- bRange args]

cMatchNode :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cMatchNode args q r = let m = annLen q - 1 in
  Eq (r![m+1]) (q![m+1]) :
  Eq (r![m+2]) (q![m+1]) :
  Eq (r!(replicate m 0 ++ [1,0,0])) (q![m+1]) :
  Eq (r!(replicate m 0 ++ [0,1,0])) (q![m+1]) :
  [Eq (r!(as ++ [a,a,b])) (q!(as ++ [a,b]))
  | as <- aIdx args m,
    a <- aRange args,
    b <- bRange args]
  ++ [Eq (q![i]) (r![i]) | i <- [1..m]]
  

cLetBase :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cLetBase args q p r p' = let m = annLen p
                             k = annLen r in
  [Eq (r!(replicate k 0 ++ [c])) (p'![c]) | c <- bRange args]
  ++ [Eq (r![j]) (q![m+j]) | j <- [1..k]] 
  ++ [Eq (p![i]) (q![i]) | i <- [1..m]]
  ++ [Eq (p!(as ++ [c])) (q!(as ++ replicate k 0 ++ [c]))
     | as <- aIdx args m,
       c <- bRange args]
  ++ [Eq (q!(replicate m 0 ++ bs ++ [c])) (r!(bs ++ [c]))
     | bs <- aIdx args k,
       bs /= replicate k 0,
       c <- bRange args]

cLet :: LogPotArgs
  -> Bool -> IndexedCoeffs -> IndexedCoeffs
  -> IndexedCoeffs -> AnnArray IndexedCoeffs
  -> AnnArray IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cLet args neg q p p' ps ps' r = let m = annLen p
                                    k = annLen r - 1
                                    _eRange = if neg then eRangeNeg args else eRange args in
  Eq (r![k+1]) (p'![1]) :
  [Eq (p![i]) (q![i]) | i <- [1..m]]
  ++ [Eq (p!(as ++ [c])) (q!(as ++ replicate k 0 ++ [c]))
     | as <- aIdx args m, c <- bRange args]
  ++ [Eq (r![j]) (q![m+j]) | j <- [1..k]]
  ++ [Eq (r!(replicate k 0 ++ [d,e])) (p'![d,e])
     | d <- aRange args, e <- bRange args] 
  ++ [Eq (r!(bs ++ [0,c])) (q!(replicate m 0 ++ bs ++ [c]))
     | bs <- aIdx args k,
       bs /= replicate k 0,
       c <- bRange args]
  ++ [EqSum (q!(as ++ bs ++ [c])) [(ps!!(bs ++ [d,e]))!(as ++ [c + max (-e) 0])
                                  | d <- delete 0 (dRange args),
                                    e <- _eRange]
     | bs <- aIdx args k,
       bs /= replicate k 0,
       as <- aIdx args m,
       as /= replicate m 0,
       c <- bRange args]
  ++ [Eq (r!(bs ++ [d,e])) (ps'!!(bs ++ [d,e])![d, max e 0])
     | bs <- aIdx args k,
       bs /= replicate k 0,
       d <- dRange args,
       d /= 0,
       e <- _eRange]
  ++ [Zero (ps'!!(bs ++ [d,e])![d',e'])
      | bs <- delete (replicate k 0) (aIdx args k),
      d <- dRange args,
      d /= 0,
      e <- _eRange,
      d' <- dRange args,
      e' <- _eRange,
      (d', e') /= (d, max e 0)]
  ++ [GeSum [ps!!(bs ++ [d,e])!(as ++ [c])
            | as <- aIdx args m, c <- bRange args]
       (ps'!!(bs ++ [d,e])![d, max e 0])
     | bs <- aIdx args k,
       bs /= replicate k 0,
       d <- delete 0 (dRange args),
       e <- _eRange]
  ++ [Impl (NotZero (ps!!(bs ++ [d,e])!(as ++ [c])))
      (Le (ps'!!(bs ++ [d,e])![d, max e 0]) (ps!!(bs ++ [d,e])!(as ++ [c])))
     | bs <- delete (replicate k 0) (aIdx args k),
     d <- dRange args,
     d /= 0,
     e <- _eRange,
     as <- aIdx args m,
     as /= replicate m 0,
     c <- bRange args]

cWeakenVar :: LogPotArgs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cWeakenVar args q r = let m = annLen r in 
  [Eq (q![i]) (r![i]) | i <- [1..m]]
  ++ [Eq (q!(as ++ [0,b])) (r!(as ++ [b])) | as <- aIdx args m, b <- bRange args]

cWeaken :: LogPotArgs ->
  [RuleArg] -> IndexedCoeffs -> IndexedCoeffs
  -> IndexedCoeffs -> IndexedCoeffs -> [Constraint]
cWeaken args ruleArgs q q' p p' = []


-- TODO accept arguments to be printed as well. 
printPot :: LogPotArgs
  -> IndexedCoeffs -> String
printPot args qs@(IndexedCoeffs len _) = rankCoeffs ++ " " ++ logCoeffs 
  where rankCoeffs = intercalate " + " [_printCoeff (qs![x]) ++ "rk(t)" | x <- [1..len]]
        logCoeffs = intercalate " + " $ map (\idx -> _printCoeff (qs!idx) ++ printLog idx) (abIdx args len)
        _printCoeff q = case printCoeff q of
          "0" -> ""
          s -> s
        printLog :: [Int] -> String
        printLog xs = "log(" ++ intercalate " + " (map show xs) ++ ")"

logPot :: LogPotArgs -> GroundPot
logPot args = Potential
  (rsrcAnn args)
  (enumAnn args)
  (forAllIdx args)
  elems
  annLen
  (cPlusConst args)
  (cMinusConst args)
  (cMinusVar args)
  (cPlusMulti args)
  (cLeaf args)
  (cNode args)
  (cPair args)
  (cMatchLeaf args)
  (cMatchNode args)
  (cLetBase args)
  (cLet args)
  (cWeakenVar args)
  (cWeaken args)
  (printPot args)
