{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.RightHeavy.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import Data.Set(Set)
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
import CostAnalysis.Constraint (Constraint, zero)
import CostAnalysis.Potential.Logarithm.Base


data Args = Args {
  aRange :: ![Int],
  bRange :: ![Int]}

potType = TreeType

-- ranges :: Args -> AnnRanges
-- ranges potArgs = AnnRanges (aRange potArgs) (bRange potArgs) (-1:bRange potArgs)

template :: Args -> Int -> Text -> Text -> [Id] -> TemplateOptions -> FreeTemplate
template potArgs id label comment args opts =
  let rangeA = aRange potArgs
      rangeB = bRange potArgs
      ghosts = ["!g1" | ghostVars opts] in
  FreeTemplate id args ghosts label comment $ S.fromList
  (map Pure args
   ++ logCoeffs args (rangeA, rangeB `L.union` [-1 | negBindingConst opts])
   ++ iversonCoeffs args ghosts rangeB)

-- x_1^(1,1) + ... + x_n^(1,1) < y^(2,1)
iversonCoeffs :: [Id] -> [Id] -> [Int] -> [CoeffIdx]
iversonCoeffs args ghosts cRange = 
  [[mix|x^(2,1),_ys|]
  | x <- args ++ ghosts,
    ys <- map S.fromList $ sums (L.delete x args) cRange,
    (not . null) ys]
    

sums :: [Id] -> [Int] -> [[Factor]]
sums args cRange = 
  concatMap (\xs -> let varFacs = map (`Arg` [1,1]) xs in
                      varFacs:[cFac:varFacs |
                               c <- cRange,
                               c /= 0,
                               let cFac = Const c])
  (varSums args)

  
varSums :: [Id] -> [[Id]]
varSums = tail . foldr (\x -> concatMap (\y -> [y,x:y])) [[]] 

oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ _ _ = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = concatMap (\i -> zero (q!i)) (mixes2 q)
  ++ zero (q![mix|1|])

letCfIdxs :: Args -> FreeTemplate -> [Id] -> TemplateOptions -> Id -> [(JudgementType, CoeffIdx)] 
letCfIdxs args q delta opts x
  = logCfIdxs (aRange args, bRange args) q delta opts x
  ++ (L.nub . concat)
  [[(CfAny, [mix|_bs,x^(1,1)|]),
    (CfAny, [mix|_bs,c,x^(1,1)|])]
  | idx <- mixes2 q,
    let rhs = varsForFac idx [2,1],
    all (`elem` delta) rhs,
    let bs = varsRestrict idx delta,
    let c = constFactor idx,
    (not . null) bs]

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "rh(" ++ T.unpack x ++ ")"
printBasePot idx = printLogTerm idx

auxSigs :: [(Measure, ProveKind)]
--auxSigs = [(Weight, Upper)]
auxSigs = []
