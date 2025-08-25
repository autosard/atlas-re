{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.TreeSize.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.Template
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..), MonoFn(..), JudgementType(..))
import CostAnalysis.Constraint (Constraint)

potType = TreeType

template :: Int -> Text -> Text -> [Id] -> TemplateOptions -> FreeTemplate
template id label comment args opts =
  FreeTemplate id args [] label comment $ S.fromList (oneCoeff:map Pure args)
               
oneCoeff :: CoeffIdx
oneCoeff = [mix|1|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ _ _ = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = []

letCfIdxs :: FreeTemplate -> [Id] -> TemplateOptions -> Id -> [(JudgementType, CoeffIdx)] 
letCfIdxs q xs opts x = []

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "|" ++ T.unpack x ++ "|"
printBasePot idx | justConst idx = show (constFactor idx)


