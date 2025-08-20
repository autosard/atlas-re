module CostAnalysis.Potential.TreeSize.Optimization(cOptimize) where

import Prelude hiding (sum)

import CostAnalysis.Template hiding (sub, sum)
import CostAnalysis.Constraint

import CostAnalysis.Coeff hiding ((^))
import qualified Data.Map as M

cOptimize :: (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Term]
cOptimize (q, _) q' = M.elems $ M.mapWithKey weighted (terms (symbolicCost q q'))
  where weighted c v = prod [ConstTerm $ coeffWeight c, v]

coeffWeight :: CoeffIdx -> Rational
coeffWeight (Pure _) = 2
coeffWeight (Mixed factors) = 1
