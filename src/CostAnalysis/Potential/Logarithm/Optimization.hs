{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Logarithm.Optimization where

import qualified Data.Set as S

import Prelude hiding (sum)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Template hiding (sub, sum)
import CostAnalysis.Constraint
import qualified CostAnalysis.Coeff as Coeff (constFactor, facForVar, (^))
import CostAnalysis.Coeff hiding ((^))


weightedAbs :: FreeTemplate -> Term
weightedAbs q = sum [prod [q!idx, ConstTerm $ indexWeight a b]
                    | idx <- mixes q,
                      let a = Coeff.facForVar idx x,
                      let b = Coeff.constFactor idx]
  where x = head (args q)


indexWeight :: Int -> Int -> Rational
indexWeight 0 2 = 0
indexWeight 1 0 = 1
indexWeight a b = fromIntegral (1 + a + (2 * (b + 1)) ) ^ 2

indexWeight' :: CoeffIdx -> Rational
indexWeight' i@(Mixed _) | justConst i = 1
indexWeight' i@(Pure _) = 100 -- often these terms are linear so we dont want them to show up.
indexWeight' i@(Mixed _) | singleVar i && idxSum i == 1 = 1
indexWeight' i@(Mixed _) = fromIntegral $
  (1 + idxSumVar i + 2 * (constFactor i + 1)) ^2


indexWeightedSum :: FreeTemplate -> Term
indexWeightedSum q = sum [prod [ConstTerm (indexWeight' i), q!i] | i <- S.toList $ idxs q]


constantDifference :: FreeTemplate -> FreeTemplate -> Term
constantDifference q q' = sub [q![mix|2|], q'!?[mix|2|]]

absRank :: FreeTemplate -> Term
absRank q = sum [q!?x | x <- args q]

absNonRank :: FreeTemplate -> Term
absNonRank q = sum [q!idx | idx <- mixes q]

