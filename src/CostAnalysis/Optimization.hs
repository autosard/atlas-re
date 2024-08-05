{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.Optimization where

import CostAnalysis.Constraint
import Control.Monad.State
import Lens.Micro.Platform
import Data.Foldable (foldrM)

type Target = (Term, [Constraint])

newtype OptimizationState = OptimizationState {
  _idGen :: Int}

makeLenses ''OptimizationState

type OptiMonad a = State OptimizationState a

freshVar :: OptiMonad Term
freshVar = do
  g <- use idGen
  idGen .= g+1
  return $ VarTerm g

bindToVars :: (Term -> a -> [Constraint]) -> [a] -> OptiMonad ([Term], [Constraint])
bindToVars binder = foldrM go ([],[])
  where go x (vars, cs) = do
          var <- freshVar
          let c = binder var x
          return (var:vars, c ++ cs ++ ge var (ConstTerm 0))

