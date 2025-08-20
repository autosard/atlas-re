{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Logarithm.Base where

import Prelude hiding ((^))

import Data.List(intercalate)
import qualified Data.Set as S
import qualified Data.Text as T

import Primitive(Id, printTerms)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff 

combi :: ([Int], [Int]) -> [Id] -> [CoeffIdx]
combi (rangeA, rangeB) xs = map (Mixed . S.fromList)$
  combi' rangeA [[Const c | c /= 0] | c <- rangeB] xs

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
printLogTerm (Mixed factors) = "log(" ++ printTerms printFac (map printTerm (S.toDescList factors)) ++ ")"
  where printTerm (Const c) = ("", c)
        printTerm (Arg x [a]) = ("|" ++ T.unpack x ++ "|", a)
        printFac 1 t | not . null $ t = t
        printFac c t = show c ++ t
