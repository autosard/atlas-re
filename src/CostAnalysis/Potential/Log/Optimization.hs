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
  let sum = Eq (VarTerm target) (Sum $ map VarTerm ds)
  return (target, varGeZero target:sum:diffs)
  where diff :: Coeff -> Var -> Id -> Constraint
        diff rankQ' d x = Eq (VarTerm d) $ Diff [CoeffTerm (q!x), CoeffTerm rankQ']


weightedNonRankDifference :: Args -> RsrcAnn -> RsrcAnn -> OptiMonad Target
weightedNonRankDifference potArgs q q' = do
  target <- freshVar
  (ds, diffs) <- bindToVars (\var (p, p', _) -> Eq (VarTerm var) $ Diff [CoeffTerm p, CoeffTerm p']) pairs
  (ws, weightedDiffs) <- bindToVars (\var (d, (_, _, (a,b))) -> Eq (VarTerm var) $ Prod [VarTerm d, ConstTerm (w a b)]) (zip ds pairs)
  let sum = Eq (VarTerm target) $ Sum (map VarTerm ws)
  return (target, varGeZero target:sum:(diffs ++ weightedDiffs))
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
  let diff = Eq (VarTerm target) $ Diff [CoeffTerm (q![mix|2|]), CoeffTerm (q'![mix|2|])]
  return (target, varGeZero target:[diff])                                     

absRank :: Args -> RsrcAnn -> OptiMonad Target
absRank potArgs q = do
  target <- freshVar
  let sum = Eq (VarTerm target) $ Sum [CoeffTerm (q!x) | x <- annVars q]
  return (target, varGeZero target:[sum])

absNonRank :: Args -> RsrcAnn -> OptiMonad Target
absNonRank potArgs q = do
  target <- freshVar
  let sum = Eq (VarTerm target) $ Sum [CoeffTerm (q!idx) | idx <- combi potArgs (annVars q)]
  return (target, varGeZero target:[sum])
  
cOptimize :: Args ->
  RsrcAnn -> RsrcAnn -> OptiMonad Target
cOptimize potArgs q q' = do
  target <- freshVar
  (subTargets, cs) <- unzip <$> sequence [
        -- rankDifference q q',
        absRank potArgs q,
        weightedNonRankDifference potArgs q q',
        constantDifference q q']
        -- absNonRank potArgs q]
  (weightedSubTargets, csWeighted) <- bindToVars (\var (target, w) -> Eq (VarTerm var) $ Prod [VarTerm target, ConstTerm w]) $ zip subTargets [179969, 16127, 997, 97, 2]
  let sum = Eq (VarTerm target) $ Sum (map VarTerm weightedSubTargets)
  return (target, varGeZero target:sum:concat cs ++ csWeighted)
