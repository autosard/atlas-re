{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Optimization(cOptimize) where

import Prelude hiding (sum)
import qualified Data.Set as S
import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Optimization
import CostAnalysis.Coeff (constFactor, facForVar)

rankDifference :: RsrcAnn -> RsrcAnn -> OptiMonad Target
rankDifference q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (diff (q'!("e" :: Id))) (annVars q)
  let cs = eq target (sum ds) ++ geZero target ++ diffs
  return (target, cs)
  where diff :: Term -> Term -> Id -> [Constraint]
        diff rankQ' d x = eq d $ sub [q!x, rankQ']


weightedAbs :: RsrcAnn -> OptiMonad Target
weightedAbs q = do
  target <- freshVar
  return (target,
          eq target (sum [prod [q!idx, ConstTerm $ indexWeight a b]
                         | idx <- mixes q,
                           let a = facForVar idx x,
                           let b = constFactor idx])
          ++ geZero target)
  where x = head (annVars q)

weightedNonRankDifference :: Args -> RsrcAnn -> RsrcAnn -> OptiMonad Target
weightedNonRankDifference potArgs q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (\var (p, p', _) -> eq var $ sub [p, p']) pairs
  (ws, weightedDiffs) <- bindToVars (\var (d, (_, _, (a,b))) -> eq var $ prod [d, ConstTerm (indexWeight a b)]) (zip ds pairs)
  return (target,
          eq target (sum ws)
          ++ geZero target
          ++ diffs
          ++ weightedDiffs)
  where pairs = [(q![mix|x^a,b|], q'![mix|y^a,b|], (a,b))
                | a <- aRange potArgs,
                  b <- bRange potArgs,
                  a + b > 0,
                  (a, b) /= (0, 2),
                  (a, b) /= (0, 1),
                  let x = annVar q,
                  let y = annVar q']
        annVar p = case annVars p of
                     [x] -> x
                     _multiArg -> error $ "Index weight is only defined for annotations of length 1." ++ show (annVars p)

indexWeight :: Int -> Int -> Rational
indexWeight 0 2 = 0
indexWeight 1 0 = 1
--indexWeight a b = fromIntegral (a + (b+1) ^ 2) ^ 2
indexWeight a b = fromIntegral (1 + a + (2 * (b + 1)) ) ^ 2


constantDifference :: RsrcAnn -> RsrcAnn -> OptiMonad Target
constantDifference q q' = do
  target <- freshVar
  return (target,
          eq target (sub [q![mix|2|], q'![mix|2|]])
          ++ geZero target)

absRank :: RsrcAnn -> OptiMonad Target
absRank q = do
  target <- freshVar
  return (target,
          eq target (sum [q!x | x <- annVars q])
          ++ geZero target)

absNonRank :: RsrcAnn -> OptiMonad Target
absNonRank q = do
  target <- freshVar
  return (target,
          eq target (sum [q!idx | idx <- mixes q])
          ++ geZero target)
  
cOptimize :: Args ->
  RsrcAnn -> RsrcAnn -> OptiMonad Target
cOptimize potArgs q q' = do
  target <- freshVar
  (subTargets, cs) <- unzip <$> sequence [
--    rankDifference q q',
--        weightedAbs q,
    absRank q,
    weightedNonRankDifference potArgs q q',
    constantDifference q q']
--    absNonRank q]
  (weightedSubTargets, csWeighted) <- bindToVars (\var (target, w) -> eq var $ prod [target, ConstTerm w]) $
    zip subTargets [179969, 16127, 997, 97, 2] --[100,100,100]--[16127, 997, 97, 2] --[179969, 16127, 997, 97, 2]
  return (target,
          geZero target
          ++ eq target (sum weightedSubTargets)
          ++ concat cs
          ++ csWeighted)
