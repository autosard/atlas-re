module CostAnalysis.Potential.RightHeavy.Optimization(cOptimize) where

import Prelude hiding (sum)

import CostAnalysis.Template hiding (sub, sum)
import CostAnalysis.Constraint
import CostAnalysis.Potential.Logarithm.Optimization

import CostAnalysis.Coeff hiding ((^))
import qualified Data.Map as M

cOptimize :: (FreeTemplate, FreeTemplate) -> FreeTemplate -> Term
cOptimize (q, _) q' = sum $ M.elems $ M.mapWithKey weighted (terms (symbolicCost q q'))
  where weighted c v = prod [ConstTerm $ indexWeight' c, v]
