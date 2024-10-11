{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Kind where

import qualified Data.Set as S

import CostAnalysis.Potential (Potential (constCoeff))
import qualified CostAnalysis.Potential.Log as Log
import qualified CostAnalysis.Potential.Poly as Poly
import qualified CostAnalysis.Potential.NLog as NLog
import CostAnalysis.AnnIdxQuoter
import Ast (PotentialKind(..))
import CostAnalysis.Coeff (CoeffIdx (Pure), Factor(..), idxToSet)


fromKind :: PotentialKind -> Potential
fromKind Logarithmic = Log.defaultPot
fromKind Polynomial = Poly.defaultPot
fromKind LinLog = NLog.defaultPot
                      
pays :: PotentialKind -> PotentialKind -> Maybe (CoeffIdx -> Maybe CoeffIdx)
pays LinLog Logarithmic = Just logToLinLog
pays _ _ = Nothing

logToLinLog :: CoeffIdx  -> Maybe CoeffIdx
logToLinLog (Pure _) = Nothing
logToLinLog idx = case S.toDescList $ idxToSet idx of
  [Arg x [1]] -> Just [mix|x^(0,1,0)|]
  [Const 2] -> Just [mix||]
  _cannotPay -> Nothing

