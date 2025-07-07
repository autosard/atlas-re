{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Kind where

import qualified Data.Set as S

import CostAnalysis.Potential (Potential)
import qualified CostAnalysis.Potential.SumOfLogs as SumOfLogs
import qualified CostAnalysis.Potential.Poly as Poly
import qualified CostAnalysis.Potential.NLog as NLog
import CostAnalysis.AnnIdxQuoter
import Ast (PotentialKind(..))
import CostAnalysis.Coeff (CoeffIdx (Pure), Factor(..), idxToSet)
import qualified CostAnalysis.Potential.Rank as Rank


fromKind :: PotentialKind -> Potential
fromKind LogR = SumOfLogs.logrPot
fromKind LogL = SumOfLogs.loglPot
fromKind LogLR = SumOfLogs.defaultPot
fromKind LogLRX = SumOfLogs.loglrxPot
fromKind Polynomial = Poly.defaultPot
fromKind LinLog = NLog.defaultPot
fromKind LogGolden = SumOfLogs.goldenPot
fromKind Rank = Rank.defaultPot
                      
pays :: PotentialKind -> PotentialKind -> Maybe (CoeffIdx -> Maybe CoeffIdx)
pays p1 p2 | p1 == p2 = Just Just
pays LinLog LogLR = Just logToLinLog
pays LinLog LogR = Just logToLinLog
pays _ _ = Nothing

logToLinLog :: CoeffIdx  -> Maybe CoeffIdx
logToLinLog (Pure _) = Nothing
logToLinLog idx = case S.toDescList $ idxToSet idx of
  [Arg x [1]] -> Just [mix|x^(0,1,0)|]
  [Const 2] -> Just [mix||]
  _cannotPay -> Nothing

