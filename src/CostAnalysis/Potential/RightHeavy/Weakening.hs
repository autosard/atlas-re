{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Potential.RightHeavy.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.Coeff



import qualified CostAnalysis.Predicate as P




supportedArgs = S.empty


genExpertKnowledge :: Set WeakenArg -> Set P.Predicate -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge wArgs preds args idxs = (V.fromList [V.fromList []], [])

