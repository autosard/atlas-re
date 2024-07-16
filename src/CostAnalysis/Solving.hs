{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module CostAnalysis.Solving where

import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization
import CostAnalysis.Potential
import Data.Ratio(numerator, denominator)
import Z3.Monad 
import CostAnalysis.RsrcAnn
import Control.Monad (mapAndUnzipM)
import Control.Monad.State (evalState)


import Data.List (intercalate)
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

class Encodeable a where
  toZ3 :: (MonadZ3 z3) => a -> z3 AST

instance Encodeable Coeff where
  toZ3 (GenCoeff id) = mkRealVar =<< mkStringSymbol ("opt_" ++ show id)
  toZ3 q@(AnnCoeff {}) = mkRealVar =<< mkStringSymbol (printCoeff q)

instance Encodeable Rational where
  toZ3 r = mkReal (fromIntegral (numerator r)) (fromIntegral (denominator r))

instance Encodeable Constraint where
  toZ3 (Eq q p) = do
    q' <- toZ3 q
    p' <- toZ3 p
    mkEq q' p'
  toZ3 (EqSum q ps) = do
    sum <- mkAdd =<< mapM toZ3 ps
    q' <- toZ3 q
    mkEq q' sum
  toZ3 (EqPlusConst q p c) = do
    q' <- toZ3 q
    p' <- toZ3 p
    c' <- toZ3 c
    sum <- mkAdd [p', c']
    mkEq q' sum
  toZ3 (EqMinusConst q p c) = do
    q' <- toZ3 q
    p' <- toZ3 p
    c' <- toZ3 c
    sub <- mkSub [p', c']
    mkEq q' sub
  toZ3 (EqMinusVar q p) = do
    q' <- toZ3 q
    p' <- toZ3 p
    k <- mkFreshRealVar "k"
    mkGe k =<< mkReal 0 1
    sub <- mkSub [p', k]
    mkEq q' sub
  toZ3 (EqPlusMulti q p r) = do
    q' <- toZ3 q
    p' <- toZ3 p
    r' <- toZ3 r
    k <- mkFreshRealVar "k"
    mkGe k =<< mkReal 0 1
    prod <- mkMul [r', k]
    sum <- mkAdd [p', prod]
    mkEq q' sum
  toZ3 (Zero q) = do
    q' <- toZ3 q
    zero <- toZ3 (0 :: Rational)
    mkEq q' zero
  toZ3 (NotZero q) = mkNot =<< toZ3 (Zero q)
  toZ3 (Le q p) = do
    q' <- toZ3 q
    p' <- toZ3 p
    mkLe q' p'
  toZ3 (GeSum qs p) = do
    p' <- toZ3 p
    sum <- mkAdd =<< mapM toZ3 qs
    mkGe sum p'
  toZ3 (Impl c1 c2) = do
    c1' <- toZ3 c1
    c2' <- toZ3 c2
    mkImplies c1' c2'
  toZ3 (EqSub q ps) = do
    q' <- toZ3 q
    sub <- mkSub =<< mapM toZ3 ps
    mkEq q' sub
  toZ3 (EqMultConst q p c) = do
    q' <- toZ3 q
    p' <- toZ3 p
    c' <- toZ3 c
    mkEq q' =<< mkMul [p', c']

    
type Solution a = Either [Constraint] (Map Coeff Rational)

genOptiTarget :: Potential -> [FunRsrcAnn] -> Target
genOptiTarget pot fns = evalState buildTarget (OptimizationState 0)
  where buildTarget = do
            target <- freshCoeff
            (targets, cs) <- mapAndUnzipM optimizeFn fns
            return (target, EqSum target targets:concat cs)
        optimizeFn fn = do
          let (q, q') = withCost fn
          cOptimize pot q q'

solveZ3 :: Potential -> RsrcSignature -> [Constraint] -> IO (Solution a)
solveZ3 pot sig cs = do
  let (optiTarget, optiCs) = genOptiTarget pot (M.elems sig)
  evalZ3 $ solveZ3' optiTarget sig (cs ++ optiCs)


evalCoeffs :: MonadZ3 z3 => Model -> [Coeff] -> z3 (Map Coeff Rational)
evalCoeffs m qs = do
  M.fromList <$> mapM evalCoeff qs
  where evalCoeff q = do
          q' <- toZ3 q
          evalResult <- evalReal m q'
          case evalResult of
            Just r -> return (q, r)
            Nothing -> error $ "Evaluation of coefficient " ++ show q ++ " in z3 model failed."

solveZ3' :: (MonadOptimize z3) => Coeff -> RsrcSignature -> [Constraint] -> z3 (Solution a)
solveZ3' target sig cs = do
  let annCoeffs = S.filter isAnnCoeff $ S.unions $ map (S.fromList . getCoeffs) cs
  annCoeffs' <- mapM toZ3 (S.toList annCoeffs)
  positiveCs <- mapM (\coeff -> mkGe coeff =<< mkReal 0 1) annCoeffs'
  mapM_ optimizeAssert positiveCs
  cs' <- mapM toZ3 cs
  target' <- toZ3 target
  -- optimizeMinimize target'
  result <- optimizeCheck cs'
  case result of
    Sat -> do
      model <- optimizeGetModel
      Right <$> evalCoeffs model (getCoeffs sig)
    Unsat -> do
      unsatCore <- optimizeGetUnsatCore
      astStrings <- mapM astToString unsatCore
      error $ "unsat: " ++ intercalate "," astStrings
    Undef -> error "Z3 returned undef."
   where isAnnCoeff (AnnCoeff {}) = True
         isAnnCoeff _ = False
   
   
  
