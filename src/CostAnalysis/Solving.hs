{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}

module CostAnalysis.Solving where

import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization
import CostAnalysis.Potential
import Data.Ratio(numerator, denominator)
import Z3.Monad 
import CostAnalysis.RsrcAnn (FunRsrcAnn(withCost))
import Control.Monad (mapAndUnzipM)
import Control.Monad.State (evalState)
import Data.List (intercalate)

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

class Encodeable a where
  toZ3 :: (MonadZ3 z3) => a -> z3 AST

instance Encodeable Coeff where
  toZ3 (GenCoeff _) = mkFreshRealVar ""
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
    sub <- mkSub [p', k]
    mkEq q' sub
  toZ3 (EqPlusMulti q p r) = do
    q' <- toZ3 q
    p' <- toZ3 p
    r' <- toZ3 r
    k <- mkFreshRealVar "k"
    sum <- mkAdd [p', k]
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

    
type Solution = Either [Constraint] (Coeff -> Rational)

genOptiTarget :: Potential a -> [FunRsrcAnn a] -> Target
genOptiTarget pot fns = evalState buildTarget (OptimizationState 0)
  where buildTarget = do
            target <- freshCoeff
            (targets, cs) <- mapAndUnzipM optimizeFn fns
            return (target, EqSum target targets:concat cs)
        optimizeFn fn = do
          let (q, q') = withCost fn
          cOptimize pot q q'

solveZ3 :: Potential a -> [FunRsrcAnn a] -> [Constraint] -> IO Solution
solveZ3 pot fns cs = do
  let (optiTarget, optiCs) = genOptiTarget pot fns
  
  evalZ3 $ solveZ3' optiTarget (cs ++ optiCs)

solveZ3' :: (MonadOptimize z3) => Coeff -> [Constraint] -> z3 Solution
solveZ3' target cs = do
   cs' <- mapM toZ3 cs
   target' <- toZ3 target
   mapM_ optimizeAssert cs'
   optimizeMinimize target'
   result <- optimizeCheck []
   case result of
     Sat -> do
       model <- optimizeGetModel
       error <$> showModel model
     Unsat -> do
       unsatCore <- optimizeGetUnsatCore
       astStrings <- mapM astToString unsatCore
       error $ intercalate "\n" astStrings
     Undef -> error "Z3 returned undef."
   
   
   
   
  
