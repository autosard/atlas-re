{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.Optimization where

import CostAnalysis.Constraint
import Control.Monad.State
import Lens.Micro.Platform
import Data.Foldable (foldrM)

type Target = (Var, [Constraint])

newtype OptimizationState = OptimizationState {
  _idGen :: Int}

makeLenses ''OptimizationState

type OptiMonad a = State OptimizationState a

freshVar :: OptiMonad Var
freshVar = do
  g <- use idGen
  idGen .= g+1
  return $ Var True g  

bindToVars :: (Var -> a -> Constraint) -> [a] -> OptiMonad ([Var], [Constraint])
bindToVars binder = foldrM go ([],[])
  where go x (vars, cs) = do
          var <- freshVar
          let c = binder var x
          return (var:vars, c:cs)

