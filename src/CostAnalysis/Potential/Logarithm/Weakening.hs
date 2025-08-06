{-# LANGUAGE TupleSections #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.Logarithm.Weakening where

import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Vector as V
import Data.Maybe(fromMaybe)
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id, infinity)
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Weakening
import CostAnalysis.Coeff 

-- \sum a_i * |x_i| + a_{n+1} <= \sum b_i * |y_i| b_{n+1}.
-- We know that arguments are trees, so we assume |x_i|,|y_i| >= 1. 
monoLe :: [(Id, Id)] -> [Id] -> CoeffIdx -> CoeffIdx -> Bool
monoLe lePreds vars i@(Mixed _) j@(Mixed _) | onlyFacsOfLen 1 i && onlyFacsOfLen 1 j
  = sum (i `subtract` j) <= 0
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

-- t >= u => log(t + u) >= log(u) + 1
logLemma2 :: [(Id, Id)] -> [Id] -> Set CoeffIdx -> LeMatrix
logLemma2 lePreds args idxs = merge $ [(V.singleton (row x xy), [0])
                                     | (x,xy) <- idxPairs]
  where iConst = S.findIndex [mix|2|] idxs
        row idxX idxXY = let iX = S.findIndex idxX idxs
                             iXY = S.findIndex idxXY idxs in
                    V.fromList [if k == iConst || k == iX then 1 else
                                   if k == iXY then -1 else 0
                               | k <- [0..length idxs -1]]
        idxPairs = [(idxX, idxXY)
                   | (x,y) <- lePreds,
                     let idxX = [mix|x^1|],
                     S.member idxX idxs,
                     let idxXY = [mix|x^1,y^1|],
                     S.member idxXY idxs]
