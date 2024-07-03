module CostAnalysis.Optimization where

import CostAnalysis.Coeff
import CostAnalysis.Constraint
import Control.Monad.State

type Target = (Coeff, [Constraint])

data OptimizationState

type OptiMonad = StateT
