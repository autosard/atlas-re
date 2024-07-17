{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Optimization(cOptimize) where

import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Coeff hiding ((^))
import CostAnalysis.Optimization

rankDifference :: RsrcAnn -> RsrcAnn -> OptiMonad Target
rankDifference q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (diff (q'!("e" :: Id))) (annVars q)
  let sum = EqSum target ds
  return (target, sum:diffs)
  where diff :: Coeff -> Var -> Id -> Constraint
        diff rankQ' d x = EqSub d [AnnCoeff (q!x), AnnCoeff rankQ']


weightedNonRankDifference :: Args -> RsrcAnn -> RsrcAnn -> OptiMonad Target
weightedNonRankDifference potArgs q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (\var (p, p', _) -> EqSub var [AnnCoeff p, AnnCoeff p']) pairs
  (ws, weightedDiffs) <- bindToVars (\var (d, (_, _, (a,b))) -> EqMultConst var d (w a b)) (zip ds pairs)
  let sum = EqSum target ws
  return (target, sum:(diffs ++ weightedDiffs))
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
        w a b = fromIntegral (a + (b+1) ^ 2) ^ 2
                       
constantDifference :: RsrcAnn -> RsrcAnn -> OptiMonad Target
constantDifference q q' = do
  target <- freshVar
  let diff = EqSub target [AnnCoeff (q![mix|2|]), AnnCoeff (q'![mix|2|])]
  return (target, [diff])                                     

absoluteValue :: Args -> RsrcAnn -> OptiMonad Target
absoluteValue potArgs q = do
  target <- freshVar
  let sum = EqSum target [AnnCoeff (q!idx) | idx <- combi potArgs (annVars q)]
  return (target, [sum])
  
cOptimize :: Args ->
  RsrcAnn -> RsrcAnn -> OptiMonad Target
cOptimize potArgs q q' = do
  target <- freshVar
  (subTargets, cs) <- unzip <$> sequence [
        rankDifference q q',
        weightedNonRankDifference potArgs q q',
        constantDifference q q',
        absoluteValue potArgs q]
  (weightedSubTargets, csWeighted) <- bindToVars (\var (target, w) -> EqMultConst var target w) $ zip subTargets [16127, 997, 97, 2]
  let sum = EqSum target weightedSubTargets
  return (target, sum:concat cs ++ csWeighted)
