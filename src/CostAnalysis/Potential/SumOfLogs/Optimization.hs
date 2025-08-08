{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.SumOfLogs.Optimization(cOptimize) where

import Prelude hiding (sum)
import qualified Data.Set as S
import qualified Data.Map as M

import CostAnalysis.Template hiding (sub, sum)
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff hiding ((^))
import CostAnalysis.Potential.SumOfLogs.Base
import qualified CostAnalysis.Coeff as Coeff (constFactor, facForVar, (^))
import CostAnalysis.Potential.Logarithm.Optimization

weightedNonRankDifference :: Args -> FreeTemplate -> FreeTemplate -> Term
weightedNonRankDifference potArgs q q' = sum $ map weightedDiff pairs 
  where weightedDiff (p, p', (a,b)) = prod [ConstTerm (indexWeight a b), sub [p, p']]
        pairs = [(q![mix|_xs,b|], q'!?[mix|_ys,b|], (a,b))
                | a <- aRange potArgs,
                  b <- bRange potArgs,
                  a + b > 0,
                  (a, b) /= (0, 2),
                  (a, b) /= (0, 1),
                  let xs = S.fromList $ map (Coeff.^a) $ args q,
                  let ys = S.fromList $ map (Coeff.^a) $ args q']

  
cOptimize :: Args -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> Term
cOptimize potArgs (q, qe) q' = let weights = [179969, 179969, 16127, 16127, 997, 97, 2] in
  sum $ zipWith (\w metric -> prod [ConstTerm w, metric]) weights [
  absRank q,
  absRank qe,
  weightedNonRankDifference potArgs q q',
  indexWeightedSum qe,
  constantDifference q q']

-- cOptimize :: Args -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> Term
-- cOptimize _ (q, _) q' = sum $ M.elems $ M.mapWithKey weighted (terms (symbolicCost q q'))
--   where weighted c v = prod [ConstTerm $ indexWeight' c, v]
