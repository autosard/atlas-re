{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.RightHeavy.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.List as L

import Primitive(Id, traceShow)
import CostAnalysis.Coeff

import CostAnalysis.Template
import CostAnalysis.Annotation(Measure(..), ProveKind(..))
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..), MonoFn(..), JudgementType(..))
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
  (map Pure args
   ++ logCoeffs args ranges
   ++ iversonCoeffs args)

-- x_1^(1,1) + ... + x_n^(1,1) < y^(2,1)
iversonCoeffs :: [Id] -> [CoeffIdx]
iversonCoeffs args = 
  [[mix|x^(2,1),_yArgs|]
  | x <- args,
    ys <- sums (L.delete x args),
    (not . null) ys,
    let yArgs = S.fromList $ map (`Arg` [1,1]) ys]

sums :: [Id] -> [[Id]]
sums = foldr (\x -> concatMap (\y -> [y,x:y])) [[]] 

oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ _ _ = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = []

letCfIdxs :: FreeTemplate -> [Id] -> ([Int], [Int]) -> Id -> [(JudgementType, CoeffIdx)] 
letCfIdxs q xs (rangeA, rangeB) x = [(Cf 0, [mix|_bs,x^d,e|])
  | idx <- mixesForVars1 q xs,
    let bs = idxToSet idx,
    (not . null) bs,
    d <- rangeA,
    e <- rangeB,
    d + max e 0 > 0]
  ++ [(Aux Weight, [mix|_bs,x^(1,1)|])
     | idx <- mixesForVars2 q xs,
       onlyFac [2,1] idx,
       let bs = idxToSet idx,
       (not . null) bs]                                   

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "rh(" ++ T.unpack x ++ ")"
printBasePot idx = printLogTerm idx

auxSigs :: [(Measure, ProveKind)]
auxSigs = [(Weight, Upper)]
