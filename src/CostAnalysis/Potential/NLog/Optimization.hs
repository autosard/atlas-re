module CostAnalysis.Potential.NLog.Optimization(cOptimize) where

import Prelude hiding (sum, prod)
import qualified Data.Map as M
import qualified Data.Set as S

import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Potential(symbolicCost)
import CostAnalysis.Coeff hiding ((^))

cOptimize :: RsrcAnn -> RsrcAnn -> Term
cOptimize q q' = sum $ M.elems $ M.mapWithKey weighted (opCoeffs (symbolicCost (q, q')))
  where weighted c v = prod [ConstTerm $ coeffWeight c, v]

coeffWeight :: CoeffIdx -> Rational
coeffWeight (Mixed factors) = Prelude.product $ map facWeight (S.toList factors)
  where facWeight :: Factor -> Rational
        facWeight (Arg _ [a1,_]) = fromIntegral (a1+1) ^ 2 
