{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Potential.Logarithm where

import Prelude hiding ((^))
import Data.List(intercalate)
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe(fromMaybe)

import Primitive(Id, infinity)
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


-- \sum a_i * |x_i| + a_{n+1} <= \sum b_i * |y_i| b_{n+1}.
-- We know that arguments are trees, so we assume |x_i|,|y_i| >= 1. 
monoLe :: [(Id, Id)] -> [Id] -> CoeffIdx -> CoeffIdx -> Bool
monoLe lePreds vars i@(Mixed _) j@(Mixed _) = sum (i `subtract` j) <= 0
  where offset = predOffset vars i j lePreds
        subtract i j = let cD = fromIntegral $ constFactor i - constFactor j in
          cD : map (subFac i j) vars
        subFac i j x = let a = facForVar i x
                           b = facForVar j x
                           sa = fromMaybe 0 (fst offset M.!? x)
                           sb = fromMaybe 0 (snd offset M.!? x) in
                          if (a - sa) - (b - sb) <= 0 then fromIntegral $ (a - sa) - (b - sb) else infinity
        
        
monoLe vars _ i j@(Pure _) = justConst i && constFactor i == 2
monoLe _ _ _ _ = False 

predOffset :: [Id] -> CoeffIdx -> CoeffIdx -> [(Id, Id)] -> (Map Id Int, Map Id Int)
predOffset vars i j = let initM = M.fromList $ map (,0) vars  in
  foldr go (initM, initM) 
  where go (x,y) (mx, my) = let a = facForVar i x
                                b = facForVar j y
                                s = min a b in
          (M.adjust (+ s) x mx, M.adjust (+ s) y my)
