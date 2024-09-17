module CostAnalysis.Potential.Poly.Optimization(cOptimize) where

import Prelude hiding (sum)
import qualified Data.Map as M

import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Potential(symbolicCost)

cOptimize :: RsrcAnn -> RsrcAnn -> Term
cOptimize q q' = sum $ M.elems (opCoeffs (symbolicCost (q, q')))
