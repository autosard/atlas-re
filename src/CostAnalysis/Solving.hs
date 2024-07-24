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
import Control.Monad (mapAndUnzipM, when)
import Control.Monad.State (evalState)


import Data.List (intercalate)
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Parsing.SmtLib(parse)

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

class Encodeable a where
  toZ3 :: (MonadZ3 z3) => a -> z3 AST

-- instance Encodeable Var where
--   toZ3 (Var pos id) = do
--     let k = "k" ++ (if pos then "+" else "") ++ "_"
--     v <- mkRealVar =<< mkStringSymbol (k ++ show id)
--     when pos (assert =<< mkGe v =<< mkReal 0 1)
--     return v
--   toZ3 (AnnCoeff q) = toZ3 q

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
  toZ3 (Zero t) = bind2 mkEq (toZ3 t) (toZ3 (0 :: Rational))
  toZ3 (Le t1 t2) = bind2 mkLe (toZ3 t1) (toZ3 t2)
  toZ3 (Ge t1 t2) = bind2 mkGe (toZ3 t1) (toZ3 t2)
  toZ3 (Impl c1 c2) = bind2 mkImplies (toZ3 c1) (toZ3 c2)
  toZ3 (Not c) = mkNot =<< toZ3 c

-- instance Encodeable Constraint where
--   toZ3 (Eq q p) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     mkEq q' p'
--   toZ3 (EqSum q ps) = do
--     sum <- mkAdd =<< mapM toZ3 ps
--     q' <- toZ3 q
--     mkEq q' sum
--   toZ3 (EqPlusConst q p c) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     c' <- toZ3 c
--     sum <- mkAdd [p', c']
--     mkEq q' sum
--   toZ3 (EqMinusConst q p c) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     c' <- toZ3 c
--     sub <- mkSub [p', c']
--     mkEq q' sub
--   toZ3 (EqMinusVar q p k) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     k' <- toZ3 k
--     sub <- mkSub [p', k']
--     mkEq q' sub
--   toZ3 (EqPlusMulti q p r k) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     r' <- toZ3 r
--     k' <- toZ3 k
--     prod <- mkMul [r', k']
--     sum <- mkAdd [p', prod]
--     mkEq q' sum
--   toZ3 (EqMulti q p k) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     k' <- toZ3 k
--     prod <- mkMul [p', k']
--     mkEq q' prod
--   toZ3 (Zero q) = do
--     q' <- toZ3 q
--     zero <- toZ3 (0 :: Rational)
--     mkEq q' zero
--   toZ3 (NotZero q) = mkNot =<< toZ3 (Zero q)
--   toZ3 (Le q p) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     mkLe q' p'
--   toZ3 (GeSum qs p) = do
--     p' <- toZ3 p
--     sum <- mkAdd =<< mapM toZ3 qs
--     mkGe sum p'
--   toZ3 (Ge k c) = do
--     k' <- toZ3 k
--     c' <- toZ3 c
--     mkGe k' c'
--   toZ3 (Impl c1 c2) = do
--     c1' <- toZ3 c1
--     c2' <- toZ3 c2
--     mkImplies c1' c2'
--   toZ3 (EqSub q ps) = do
--     q' <- toZ3 q
--     sub <- mkSub =<< mapM toZ3 ps
--     mkEq q' sub
--   toZ3 (EqMultConst q p c) = do
--     q' <- toZ3 q
--     p' <- toZ3 p
--     c' <- toZ3 c
--     mkEq q' =<< mkMul [p', c']
--   toZ3 (FarkasA p fas q) = do
--     p' <- toZ3 p
--     q' <- toZ3 q
--     prods <- mapM prodToZ3 fas
--     mkLe p' =<< mkAdd (q':prods)
--     where prodToZ3 :: (MonadZ3 z3) => (Var, Int) -> z3 AST
--           prodToZ3 (x,y) = do
--             x' <- toZ3 x
--             y' <- mkReal y 1
--             mkMul [x', y']
    
type Solution a = Either [Constraint] (Map Coeff Rational)

genOptiTarget :: Potential -> [FunRsrcAnn] -> Int -> Target
genOptiTarget pot fns varIdGen = evalState buildTarget (OptimizationState varIdGen)
  where buildTarget = do
            target <- freshVar
            (targets, cs) <- mapAndUnzipM optimizeFn fns
            return (target, Eq (VarTerm target) (Sum (map VarTerm targets)):concat cs)
        optimizeFn fn = do
          let (q, q') = withCost fn
          cOptimize pot q q'

solveZ3 :: Potential -> RsrcSignature -> [Constraint] -> Int -> IO (Solution a)
solveZ3 pot sig cs varIdGen = do
  let (optiTarget, optiCs) = genOptiTarget pot (M.elems sig) varIdGen
  evalZ3 $ solveZ3' optiTarget sig (cs ++ optiCs)


evalCoeffs :: MonadZ3 z3 => Model -> [Coeff] -> z3 (Map Coeff Rational)
evalCoeffs m qs = do
  M.fromList <$> mapM evalCoeff qs
  where evalCoeff q = do
          q' <- toZ3 (CoeffTerm q)
          evalResult <- evalReal m q'
          case evalResult of
            Just r -> return (q, r)
            Nothing -> error $ "Evaluation of coefficient " ++ show q ++ " in z3 model failed."

solveZ3' :: (MonadZ3 z3) => Var -> RsrcSignature -> [Constraint] -> z3 (Solution a)
solveZ3' target sig cs = do
  let annCoeffs = S.unions $ map (S.fromList . getCoeffs) cs
  annCoeffs' <- mapM (toZ3 . CoeffTerm) (S.toList annCoeffs)
  positiveCs <- mapM (\coeff -> mkGe coeff =<< mkReal 0 1) annCoeffs'
  mapM_ assert positiveCs
  cs' <- mapM toZ3 cs
  target' <- toZ3 (VarTerm target)
  --optimizeMinimize target'

--  astStrings <- mapM astToString cs'
  t <- mkReal 2 1
  assert =<< mkLe target' t
  --mapM_ assert cs'
  --error =<< solverToString
  result <- checkAssumptions cs'
  case result of
    Sat -> do
      maybeModel <- snd <$> getModel
      let model = case maybeModel of
                    Just model -> model
                    Nothing -> error "bug"
      --error =<< modelToString model
      Right <$> evalCoeffs model (getCoeffs sig)
    Unsat -> do
      unsatCore <- getUnsatCore
      astStrings <- mapM astToString unsatCore
      return $ Left (map parse astStrings)
    Undef -> error "Z3 returned undef."  
   
  
