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

import Primitive(Id)
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Weakening
import CostAnalysis.Coeff 

monoLe :: [(Id, Id)] -> [Id] -> CoeffIdx -> CoeffIdx -> Bool
monoLe lePreds vars i@(Mixed _) j@(Mixed _) | onlyFacsOfLen 1 i && onlyFacsOfLen 1 j
  = let p = a `sub` b
        q = c `sub` d
        k = constFactor j - constFactor i in
      (
        (p `sub` q) `le` 0
        && sum p - sum q <= k)
      ||
      (
        p `le` 0 
        && sum p <= k)
  where a = V.fromList $ map (facForVar i) vars
        b = V.fromList $ map (facForVar j) vars
        offset = predOffset vars lePreds
        c = V.fromList $ map (\x -> fromMaybe 0 (fst offset M.!? x)) vars
        d = V.fromList $ map (\x -> fromMaybe 0 (snd offset M.!? x)) vars
        add = V.zipWith (+)
        sub = V.zipWith (-)
        sum = V.foldr (+) 0
        le v x = V.all (<= x) v
monoLe vars _ i j@(Pure _) = justConst i && constFactor i == 2
monoLe _ _ _ _ = False

predOffset :: [Id] -> [(Id, Id)] -> (Map Id Int, Map Id Int)
predOffset vars = let initM = M.fromList $ map (,0) vars  in
  foldr go (initM, initM) 
  where go (x,y) (mLhs, mRhs) = 
          (M.adjust (+ 1) x mLhs, M.adjust (+ 1) y mRhs)


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
