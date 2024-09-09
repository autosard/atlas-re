{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Optimization(cOptimize) where

import qualified Data.Set as S

import Prelude hiding (sum)
import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import qualified CostAnalysis.Coeff as Coeff (constFactor, facForVar, (^))

rankDifference :: RsrcAnn -> RsrcAnn -> Term
rankDifference q q' = sum $ map (diff (q'!("e" :: Id))) (annVars q)
  where diff :: Term -> Id -> Term
        diff rankQ' x = sub [q!x, rankQ']

weightedAbs :: RsrcAnn -> Term
weightedAbs q = sum [prod [q!idx, ConstTerm $ indexWeight a b]
                    | idx <- mixes q,
                      let a = Coeff.facForVar idx x,
                      let b = Coeff.constFactor idx]
  where x = head (annVars q)

weightedNonRankDifference :: Args -> RsrcAnn -> RsrcAnn -> Term
weightedNonRankDifference potArgs q q' = sum $ map weightedDiff pairs 
  where weightedDiff (p, p', (a,b)) = prod [ConstTerm (indexWeight a b), sub [p, p']]
        pairs = [(q![mix|_xs,b|], q'![mix|_ys,b|], (a,b))
                | a <- aRange potArgs,
                  b <- bRange potArgs,
                  a + b > 0,
                  (a, b) /= (0, 2),
                  (a, b) /= (0, 1),
                  let xs = S.fromList $ map (Coeff.^a) $ annVars q,
                  let ys = S.fromList $ map (Coeff.^a) $ annVars q']

indexWeight :: Int -> Int -> Rational
indexWeight 0 2 = 0
indexWeight 1 0 = 1
--indexWeight a b = fromIntegral (a + (b+1) ^ 2) ^ 2
indexWeight a b = fromIntegral (1 + a + (2 * (b + 1)) ) ^ 2


constantDifference :: RsrcAnn -> RsrcAnn -> Term
constantDifference q q' = sub [q![mix|2|], q'![mix|2|]]

absRank :: RsrcAnn -> Term
absRank q = sum [q!x | x <- annVars q]

absNonRank :: RsrcAnn -> Term
absNonRank q = sum [q!idx | idx <- mixes q]
  
cOptimize :: Args -> RsrcAnn -> RsrcAnn -> Term
cOptimize potArgs q q' = let weights = [179969, 16127, 997, 97, 2] in
  sum $ zipWith (\w metric -> prod [ConstTerm w, metric]) weights [
  rankDifference q q',
--        weightedAbs q,
  absRank q,
  weightedNonRankDifference potArgs q q',
  constantDifference q q',
  absNonRank q]  
