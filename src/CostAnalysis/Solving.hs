{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Solving where

import Prelude hiding (sum)
import Primitive(Id)
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization
import CostAnalysis.Potential
import Data.Ratio(numerator, denominator)
import Z3.Monad 
import CostAnalysis.RsrcAnn
import Control.Monad (mapAndUnzipM, (<=<))
import Control.Monad.State (evalState)

import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace (trace)
import Data.Foldable (foldrM)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

class Encodeable a where
  toZ3 :: (MonadZ3 z3) => a -> z3 AST

instance Encodeable Coeff where
  toZ3 q = mkRealVar =<< mkStringSymbol (printCoeff q)

instance Encodeable Rational where
  toZ3 r = mkReal (fromIntegral (numerator r)) (fromIntegral (denominator r))

instance Encodeable Term where
  toZ3 (VarTerm id) = mkRealVar =<< mkStringSymbol ("k_" ++ show id)
  toZ3 (CoeffTerm q) = toZ3 q
  toZ3 (Sum terms) = mkAdd =<< mapM toZ3 terms
  toZ3 (Diff terms) = mkSub =<< mapM toZ3 terms
  toZ3 (Prod terms) = mkMul =<< mapM toZ3 terms
  toZ3 (ConstTerm c) = toZ3 c

bind2 :: Monad m => (t1 -> t2 -> m b) -> m t1 -> m t2 -> m b
bind2 f g h = do
  x <- g
  y <- h
  f x y

instance Encodeable Constraint where
  toZ3 (Eq t1 t2) = bind2 mkEq (toZ3 t1) (toZ3 t2)
  toZ3 (Le t1 t2) = bind2 mkLe (toZ3 t1) (toZ3 t2)
  toZ3 (Ge t1 t2) = bind2 mkGe (toZ3 t1) (toZ3 t2)
  toZ3 (Impl c1 c2) = bind2 mkImplies (toZ3 c1) (toZ3 c2)
  toZ3 (Not c) = mkNot =<< toZ3 c

type Solution a = Either [Constraint] (Map Coeff Rational)

genOptiTarget :: Potential -> [FunRsrcAnn] -> Int -> Target
genOptiTarget pot fns varIdGen = evalState buildTarget (OptimizationState varIdGen)
  where buildTarget = do
            target <- freshVar
            (targets, cs) <- mapAndUnzipM optimizeFn fns
            return (target, eq target (sum targets) ++ concat cs)
        optimizeFn fn = do
          let (q, q') = withCost fn
          cOptimize pot q q'


evalCoeffs :: MonadZ3 z3 => Model -> [Coeff] -> z3 (Map Coeff Rational)
evalCoeffs m qs = do
  M.fromList <$> mapM evalCoeff qs
  where evalCoeff q = do
          q' <- toZ3 (CoeffTerm q)
          evalResult <- evalReal m q'
          case evalResult of
            Just r -> return (q, r)
            Nothing -> error $ "Evaluation of coefficient " ++ show q ++ " in z3 model failed."

assertConstraints :: MonadZ3 z3 => [Constraint] -> z3 (Map String Constraint)
assertConstraints = foldrM go M.empty
  where go :: MonadZ3 z3 => Constraint -> Map String Constraint -> z3 (Map String Constraint)
        go c@(Ge (VarTerm k) (ConstTerm 0)) tracker = do
          assert =<< toZ3 c
          return tracker
        go c tracker = do
          p <- mkFreshBoolVar "c"
          pS <- astToString p
          c' <- toZ3 c
--          assert p
          solverAssertAndTrack c' p
          return $ M.insert pS c tracker

assertCoeffsPos :: (MonadZ3 z3) => [Constraint] -> z3 ()
assertCoeffsPos cs = do
  let annCoeffs = S.unions $ map (S.fromList . getCoeffs) cs
  annCoeffs' <- mapM (toZ3 . CoeffTerm) (S.toList annCoeffs)
  positiveCs <- mapM (\coeff -> mkGe coeff =<< mkReal 0 1) annCoeffs'
  mapM_ assert positiveCs

-- checkSolution :: RsrcSignature -> [Constraint]
-- checkSolution sig = let t = "t" :: Id
--                         e = "e" :: Id in
--   [Eq (CoeffTerm (Coeff 0 "Q" "log" (Pure t))) (ConstTerm (1 % 2)),
--   Eq (CoeffTerm (Coeff 0 "Q" "log" (Mixed [mix|t^1|]))) (ConstTerm (3 % 2)),
--   Eq (CoeffTerm (Coeff 0 "Q" "log" (Mixed [mix|t^1,2|]))) (ConstTerm (0 % 1)),
--   Eq (CoeffTerm (Coeff 0 "Q" "log" (Mixed [mix|2|]))) (ConstTerm (1 % 1)),
--   Eq (CoeffTerm (Coeff 1 "Q'" "log" (Pure e))) (ConstTerm (1 % 2)),
--   Eq (CoeffTerm (Coeff 1 "Q'" "log" (Mixed [mix|e^1|]))) (ConstTerm (0 % 1)),
--   Eq (CoeffTerm (Coeff 1 "Q'" "log" (Mixed [mix|e^1,2|]))) (ConstTerm (0 % 1)),
--   Eq (CoeffTerm (Coeff 1 "Q'" "log" (Mixed [mix|2|]))) (ConstTerm (1 % 1))]
  -- [Le (CoeffTerm (Coeff 0 "Q" "log" (Pure t))) (ConstTerm (1 % 1)),
  -- Le (CoeffTerm (Coeff 0 "Q" "log" (Mixed [mix|t^1|]))) (ConstTerm (3 % 2)),
  -- Le (CoeffTerm (Coeff 0 "Q" "log" (Mixed [mix|t^1,2|]))) (ConstTerm (0 % 1)),
  -- Le (CoeffTerm (Coeff 0 "Q" "log" (Mixed [mix|2|]))) (ConstTerm (0 % 1)),
  -- Le (CoeffTerm (Coeff 1 "Q'" "log" (Pure e))) (ConstTerm (1 % 1)),
  -- Le (CoeffTerm (Coeff 1 "Q'" "log" (Mixed [mix|e^1|]))) (ConstTerm (0 % 1)),
  -- Le (CoeffTerm (Coeff 1 "Q'" "log" (Mixed [mix|e^1,2|]))) (ConstTerm (0 % 1)),
  -- Le (CoeffTerm (Coeff 1 "Q'" "log" (Mixed [mix|2|]))) (ConstTerm (0 % 1))]

setRankEqual :: RsrcSignature -> [Constraint]
setRankEqual sig = let t = "t" :: Id
                       e = "e" :: Id in
  [Eq (CoeffTerm (Coeff 0 "Q" "log" (Pure t))) (CoeffTerm (Coeff 1 "Q'" "log" (Pure e))) ]

dumpSMT :: Potential -> RsrcSignature -> [Constraint] -> Int -> IO ()
dumpSMT pot sig cs varIdGen = do
  writeFile "constraints.smt" =<< evalZ3 go
  where go = do
          let (optiTarget, optiCs) = genOptiTarget pot (M.elems sig) varIdGen
          assertCoeffsPos cs
          mapM_ (assert <=< toZ3) (cs ++ optiCs)
          solverToString
          

solveZ3 :: Potential -> RsrcSignature -> [Constraint] -> Int -> IO (Solution a)
solveZ3 pot sig typingCs varIdGen = evalZ3 go
  where go = do
          let (optiTarget, optiCs) = genOptiTarget pot (M.elems sig) varIdGen
          assertCoeffsPos typingCs
          --let solutionCheck = checkSolution sig
          let rankEqual = setRankEqual sig
          tracker <- assertConstraints (typingCs ++ optiCs ++ rankEqual) -- ++ solutionCheck)
          target' <- toZ3 optiTarget
          optimizeMinimize target'

          result <- check
          case result of
            Sat -> do
              maybeModel <- snd <$> getModel
              let model = case maybeModel of
                            Just model -> model
                            Nothing -> error "bug"
              solution <- modelToString model
              Right <$> evalCoeffs (trace solution model) (getCoeffs sig)
              --Right <$> evalCoeffs model (getCoeffs sig)
            Unsat -> do
              unsatCore <- getUnsatCore
              astStrings <- mapM astToString unsatCore
              return $ Left (map (tracker M.!) astStrings)
            Undef -> error "Z3 returned undef."
  

