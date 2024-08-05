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

rankDifference :: RsrcAnn -> RsrcAnn -> OptiMonad Target
rankDifference q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (diff (q'!("e" :: Id))) (annVars q)
  let cs = eq target (sum ds) ++ geZero target ++ diffs
  return (target, cs)
  where diff :: Term -> Term -> Id -> [Constraint]
        diff rankQ' d x = eq d $ sub [q!x, rankQ']


weightedNonRankDifference :: Args -> RsrcAnn -> RsrcAnn -> OptiMonad Target
weightedNonRankDifference potArgs q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (\var (p, p', _) -> eq var $ sub [p, p']) pairs
  (ws, weightedDiffs) <- bindToVars (\var (d, (_, _, (a,b))) -> eq var $ prod [d, ConstTerm (w a b)]) (zip ds pairs)
  return (target,
          eq target (sum ws)
          ++ geZero target
          ++ diffs
          ++ weightedDiffs)
  where pairs = [(q![mix|x^a,b|], q'![mix|y^a,b|], (a,b))
                | a <- aRange potArgs,
                  b <- bRange potArgs,
                  (a, b) /= (0, 2),
                  let x = annVar q,
                  let y = annVar q']
        annVar p = case annVars p of
                     [x] -> x
                     _multiArg -> error $ "Index weight is only defined for annotations of length 1." ++ show (annVars p)
        w :: Int -> Int -> Rational
        w 0 2 = 0
        w 1 0 = 1
--        w a b = fromIntegral (a + (b+1) ^ 2) ^ 2
        w a b = fromIntegral (1 + a + (2 * (b + 1)) ) ^ 2
                       
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
          eq target (sum [q!idx | idx <- S.toList $ definedIdxs q])
          ++ geZero target)
  
cOptimize :: Args ->
  RsrcAnn -> RsrcAnn -> OptiMonad Target
cOptimize potArgs q q' = do
  target <- freshVar
  (subTargets, cs) <- unzip <$> sequence [
        -- rankDifference q q',
        absRank q,
        weightedNonRankDifference potArgs q q',
        constantDifference q q']
        -- absNonRank q]
  (weightedSubTargets, csWeighted) <- bindToVars (\var (target, w) -> eq var $ prod [target, ConstTerm w]) $
    zip subTargets [179969, 16127, 997, 97, 2]
  return (target,
          geZero target
          ++ eq target (sum weightedSubTargets)
          ++ concat cs
          ++ csWeighted)
