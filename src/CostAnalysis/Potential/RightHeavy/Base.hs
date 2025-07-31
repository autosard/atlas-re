{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.RightHeavy.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.Template
import CostAnalysis.Annotation(Measure(..), ProveKind(..))
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..), MonoFn(..))
import CostAnalysis.Constraint (Constraint)
import CostAnalysis.Potential.Logarithm.Base


data Args = Args {
  aRange :: ![Int],
  bRange :: ![Int]}

potType = TreeType

ranges :: Args -> AnnRanges
ranges potArgs = AnnRanges (aRange potArgs) (bRange potArgs) (-1:bRange potArgs)

template :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> FreeTemplate
template id label comment args ranges =
  FreeTemplate id args label comment $ S.fromList
  (oneCoeff:map Pure args ++ logCoeffs args ranges)
               
oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ _ _ = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = []

letCfIdxs :: FreeTemplate -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
letCfIdxs q xs (rangeA, rangeB) x = [[mix|_bs,x^d,e|]
  | idx <- mixesForVars q xs,
    let bs = idxToSet idx,
    (not . null) bs,
    d <- rangeA,
    e <- rangeB,
    d + max e 0 > 0]

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "rh(" ++ T.unpack x ++ ")"
printBasePot idx = printLogTerm idx

auxSigs :: [(Measure, ProveKind)]
auxSigs = [(Weight, Lower), (Weight, Upper)]
