module CostAnalysis.Potential.Poly.Optimization(cOptimize) where

import Prelude hiding (sum, prod)
import qualified Data.Map as M
import qualified Data.Set as S

import CostAnalysis.Template hiding (sum)
import CostAnalysis.Constraint
import CostAnalysis.Coeff hiding ((^))

cOptimize :: (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Term]
cOptimize (q, _) q' = M.elems $ M.mapWithKey weighted (terms (symbolicCost q q'))
  where weighted c v = prod [ConstTerm $ coeffWeight c, v]

coeffWeight :: CoeffIdx -> Rational
coeffWeight (Mixed factors) = Prelude.product $ map facWeight (S.toList factors)
  where facWeight :: Factor -> Rational
        facWeight (Arg _ [a]) = fromIntegral (a+1)  --fromIntegral (a+1) ^ 2
