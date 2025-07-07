{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Rank.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.Template
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..), MonoFn(..))
import CostAnalysis.Constraint (Constraint)


-- data Args = Args {}

potType = TreeType

ranges :: AnnRanges
ranges = AnnRanges [] [] []

template :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> FreeTemplate
template id label comment args ranges =
  FreeTemplate id args label comment $ S.fromList (oneCoeff:map Pure args)
               
oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ _ _ = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = []

letCfIdxs :: FreeTemplate -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
letCfIdxs q xs (rangeA, rangeB) x = []

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "†" ++ T.unpack x 


