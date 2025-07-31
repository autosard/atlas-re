{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Logarithm.Base where

import Prelude hiding ((^))

import Data.List(intercalate)
import qualified Data.Set as S
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff 

combi :: ([Int], [Int]) -> [Id] -> [CoeffIdx]
combi (rangeA, rangeB) xs = map (Mixed . S.fromList)$
  combi' rangeA [[Const c | c > 0] | c <- rangeB] xs

varCombi :: [Int] -> [Id] -> [CoeffIdx]
varCombi rangeA xs = map (Mixed . S.fromList) $ combi' rangeA [[]] xs

combi' :: [Int] -> [[Factor]] -> [Id] -> [[Factor]]
combi' _ z [] = z
combi' rangeA z (x:xs) = [if a > 0 then x^a:y else y
                       | a <- rangeA, y <- combi' rangeA z xs]

logCoeffs :: [Id] -> ([Int], [Int]) -> [CoeffIdx]
logCoeffs args ranges = [idx
                       | idx <- combi ranges args,
                         idxSum idx > 0,
                         idx /= [mix|1|]]


printLogTerm :: CoeffIdx -> String
printLogTerm (Mixed factors) = "log(" ++ intercalate " + " (map printFactor (S.toDescList factors)) ++ ")"
  where printFactor (Const c) = show c
        printFactor (Arg x [a]) = if a /= 1 then show a ++ "|" ++ T.unpack x ++ "|" else "|" ++ T.unpack x ++ "|"
