{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.Optimization where

import CostAnalysis.Constraint
import CostAnalysis.Coeff
import Control.Monad.State
import Lens.Micro.Platform
import Data.Foldable (foldrM)

type Target = (Coeff, [Constraint])

newtype OptimizationState = OptimizationState {
  _idGen :: Int}

makeLenses ''OptimizationState

type OptiMonad a = State OptimizationState a

freshCoeff :: OptiMonad Coeff
freshCoeff = do
  g <- use idGen
  idGen .= g+1
  return $ GenCoeff g

bindToCoeffs :: (Coeff -> a -> Constraint) -> [a] -> OptiMonad ([Coeff], [Constraint])
bindToCoeffs binder = foldrM go ([],[])
  where go x (coeffs, cs) = do
          coeff <- freshCoeff
          let c = binder coeff x
          return (coeff:coeffs, c:cs)

