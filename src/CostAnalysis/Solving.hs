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

assertConstraints :: MonadOptimize z3 => [Constraint] -> z3 (Map String Constraint)
assertConstraints = foldrM go M.empty
  where go :: MonadOptimize z3 => Constraint -> Map String Constraint -> z3 (Map String Constraint)
        go c@(Ge (VarTerm k) (ConstTerm 0)) tracker = do
          assert =<< toZ3 c
          return tracker
        go c tracker = do
          p <- mkFreshBoolVar "c"
          pS <- astToString p
          c' <- toZ3 c
          solverAssertAndTrack c' p
          return $ M.insert pS c tracker

assertCoeffsPos :: (MonadOptimize z3) => [Constraint] -> z3 ()
assertCoeffsPos cs = do
  let annCoeffs = S.unions $ map (S.fromList . getCoeffs) cs
  annCoeffs' <- mapM (toZ3 . CoeffTerm) (S.toList annCoeffs)
  positiveCs <- mapM (\coeff -> mkGe coeff =<< mkReal 0 1) annCoeffs'
  mapM_ assert positiveCs

-- setRankEqual :: RsrcSignature -> [Constraint]
-- setRankEqual sig = concatMap setRankEqual' (M.elems sig) 

-- setRankEqual' :: FunRsrcAnn -> [Constraint]
-- setRankEqual' ann = eq (q!Pure x) (q'!Pure y)
--   where (q, q') = withCost ann
--         x = head $ annVars q
--         y = head $ annVars q'

-- dumpSMT :: Potential -> RsrcSignature -> [Constraint] -> Int -> IO ()
-- dumpSMT pot sig cs varIdGen = do
--   writeFile "constraints.smt" =<< evalZ3 go
--   where go = do
--           let (optiTarget, optiCs) = genOptiTarget pot (M.elems sig) varIdGen
--           assertCoeffsPos cs
--           mapM_ (assert <=< toZ3) (cs ++ optiCs)
--           solverToString

solve :: [Id] -> ProveMonad Solution
solve fns = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  opti <- sum <$> use optiTargets
--  extCs <- (setRankEqual sig' ++) <$> use sigCs
  extCs <- use sigCs
  cs <- use constraints
  result <- liftIO $ evalZ3 $ solveZ3 sig' cs extCs opti
  solution <- case result of 
    Left unsatCore -> throwError $ UnsatErr unsatCore
    Right solution -> return solution
  constraints .= []
  return solution

solveZ3 :: MonadOptimize z3 => RsrcSignature -> [Constraint] -> [Constraint] -> Term
  -> z3 (Either [Constraint] Solution)
solveZ3 sig typingCs extCs optiTarget = do
  assertCoeffsPos typingCs
  tracker <- assertConstraints (typingCs ++ extCs)
  target' <- toZ3 optiTarget
  optimizeMinimize target'
  result <- check
  case result of
    Sat -> do
      maybeModel <- snd <$> getModel
      let model = case maybeModel of
                    Just model -> model
                    Nothing -> error "bug: z3 returned sat, but no model."
      solution <- modelToString model
      Right <$> evalCoeffs model (getCoeffs sig)
    Unsat -> do
      unsatCore <- getUnsatCore
      astStrings <- mapM astToString unsatCore
      return $ Left (map (tracker M.!) astStrings)
    Undef -> error "Z3 returned undef."
  

