module CostAnalysis.Potential.Poly.Weakening where

import Data.Set(Set)
import qualified Data.Vector as V

import Primitive(Id)
import CostAnalysis.Rules(WeakenArg)
import CostAnalysis.Coeff
import CostAnalysis.Potential
import CostAnalysis.Predicate (Predicate)

genExpertKnowledge :: Set WeakenArg -> Set Predicate -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge _ _ _ _ = (V.empty, [])
