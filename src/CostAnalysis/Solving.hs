{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Solving where

import Prelude hiding (sum)
import Data.Ratio(numerator, denominator)
import Z3.Monad 

import Control.Monad.State
import Control.Monad.Except
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable (foldrM)
import Lens.Micro.Platform

import Primitive(Id)
import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.ProveMonad
import Control.Monad.Extra (whenJust)
import Data.Maybe (isNothing)

import Debug.Trace

class Encodeable a where
  toZ3 :: (MonadOptimize z3) => a -> z3 AST

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
  toZ3 (Minus term) = mkUnaryMinus =<< toZ3 term
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
  toZ3 (Or cs) = mkOr =<< mapM toZ3 cs
  toZ3 (And cs) = mkAnd =<< mapM toZ3 cs
  toZ3 (Not c) = mkNot =<< toZ3 c

evalCoeffs :: MonadOptimize z3 => Model -> [Coeff] -> z3 (Map Coeff Rational)
evalCoeffs m qs = do
  M.fromList <$> mapM evalCoeff qs
  where evalCoeff q = do
          q' <- toZ3 (CoeffTerm q)
          evalResult <- evalReal m q'
          case evalResult of
            Just r -> return (q, r)
            Nothing -> error $ "Evaluation of coefficient " ++ show q ++ " in z3 model failed."

assertConstraints :: MonadOptimize z3 => Bool -> [Constraint] -> z3 (Map String Constraint)
assertConstraints track = foldrM (go track) M.empty 
  where go :: Bool -> MonadOptimize z3 => Constraint -> Map String Constraint -> z3 (Map String Constraint)
        go False c tracker = do
          optimizeAssert =<< toZ3 c
          return tracker
        go True c@(Ge (VarTerm k) (ConstTerm 0)) tracker = do
          optimizeAssert =<< toZ3 c
          return tracker
        go True c tracker = do
          p <- mkFreshBoolVar "c"
          pS <- astToString p
          c' <- toZ3 c
          optimizeAssertAndTrack c' p
          return $ M.insert pS c tracker

assertCoeffsPos :: (MonadOptimize z3) => [Constraint] -> z3 ()
assertCoeffsPos cs = do
  let annCoeffs = S.unions $ map (S.fromList . getCoeffs) cs
  annCoeffs' <- mapM (toZ3 . CoeffTerm) (S.toList annCoeffs)
  positiveCs <- mapM (\coeff -> mkGe coeff =<< mkReal 0 1) annCoeffs'
  mapM_ optimizeAssert positiveCs

solve :: [Id] -> ProveMonad Solution
solve fns = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  targets <- use optiTargets
  let opti = case targets of
               [] -> Nothing
               ts -> Just . sum $ ts
  extCs <- use sigCs
  cs <- use constraints
  let dump = True
  (result, smt) <- liftIO . evalZ3 $
    do
      tracker <- createSolverZ3 sig' cs extCs opti
      smt <- if dump then Just <$> optimizeToString else return Nothing
      result <- solveZ3 tracker sig'
      return (result, smt)
  liftIO $ whenJust smt (writeFile "out/instance.smt")
  solution <- case result of 
    Left unsatCore -> throwError $ UnsatErr unsatCore
    Right solution -> return solution
  constraints .= []
  return (trace (concat $ M.mapWithKey showSol solution) solution)
  --return solution

showSol q v = show q ++ " = " ++ show v ++ "\n"

createSolverZ3 :: MonadOptimize z3 => RsrcSignature -> [Constraint] -> [Constraint] -> Maybe Term -> z3 (Map String Constraint)
createSolverZ3 sig typingCs extCs optiTarget = do
  assertCoeffsPos (typingCs ++ extCs)
  tracker <- assertConstraints (isNothing optiTarget) $ typingCs ++ extCs
  case optiTarget of
    Just target -> do
      target' <- toZ3 target
      optimizeMinimize target'
      return tracker
    Nothing -> return tracker

solveZ3 :: MonadOptimize z3 => Map String Constraint -> RsrcSignature -> z3 (Either [Constraint] Solution)
solveZ3 tracker sig = do
  result <- optimizeCheck []
  case result of
    Sat -> do
      model <- optimizeGetModel
--      Right <$> evalCoeffs model (concatMap getCoeffs (M.elems tracker))
      Right <$> evalCoeffs model (getCoeffs sig)
    Unsat -> do
      unsatCore <- optimizeGetUnsatCore
      astStrings <- mapM astToString unsatCore
      return $ Left (map (tracker M.!) astStrings)
    Undef -> do
      bound <- astToString =<< optimizeGetLower 0
      error $ "Z3 returned undef. " ++ "Bound: " ++ show bound 
  

