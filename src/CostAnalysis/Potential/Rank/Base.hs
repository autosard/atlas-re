{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Rank.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.List as L

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.Template
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (MonoFn(..), JudgementType(..))
import CostAnalysis.Constraint (Constraint, zero)
import CostAnalysis.Potential.Logarithm.Base

data Args = Args {
  aRange :: ![Int],
  bRange :: ![Int]}
  
potType = TreeType

template :: Args -> Int -> Text -> Text -> [Id] -> TemplateOptions -> FreeTemplate
template potArgs id label comment args opts =
  let rangeA = aRange potArgs
      rangeB = bRange potArgs in
  FreeTemplate id args [] label comment $ S.fromList
  (map Pure args
  ++ logCoeffs args (rangeA, rangeB `L.union` [-1 | negBindingConst opts]))
               
oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ _ _ = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = zero (q![mix|1|])
  ++ zero (q'![mix|1|])

letCfIdxs :: Args -> FreeTemplate -> [Id] -> TemplateOptions -> Id -> [(JudgementType, CoeffIdx)] 
letCfIdxs args = logCfIdxs (aRange args, bRange args)

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "†" ++ T.unpack x 
printBasePot idx = printLogTerm idx

