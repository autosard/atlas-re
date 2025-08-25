{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Potential.Poly.Base where

import Prelude hiding ((^))
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Set as S

import Primitive(Id)
import Typing.Type
import qualified CostAnalysis.Potential as P
import CostAnalysis.Coeff
import CostAnalysis.Template
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Constraint (Constraint)

newtype Args = Args { degree :: Int }

types = [ListType]

nestedError = error "Polynomial potential only supports simple (non-nested) inductive data types."

degrees potArgs = [0..degree potArgs]

genIdxs :: Int -> Int -> [[Int]]
genIdxs _ 0 = return []
genIdxs d l = do
  nxt <- [0..d]
  (nxt :) <$> genIdxs (d - nxt) (l - 1) 

template :: Args -> Int -> Text -> Text -> [Id] -> TemplateOptions -> FreeTemplate
template potArgs id label comment args opts =
  FreeTemplate id args [] label comment $ S.fromList coeffs
  where coeffs = map (mixed . S.fromList . zipWith (^) args)
          $ genIdxs (last (degrees potArgs)) (length args)
          
oneCoeff :: CoeffIdx
oneCoeff = [mix||]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

monoFnCoeff :: P.MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff _ args c = Nothing

cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = []

letCfIdxs :: FreeTemplate -> [Id] -> TemplateOptions -> Id -> [(P.JudgementType, CoeffIdx)] 
letCfIdxs q xs opts x = map (P.Cf 0,) $
  filter (not . null . idxToSet ) $ mixesForVars q xs

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = error "pure coefficients are not supported with polynomial potential."
printBasePot (Mixed factors) = concatMap printFactor (S.toDescList factors)
  where printFactor (Arg x [a]) = if a > 1 then
          "[|" ++ T.unpack x ++ "| " ++ show a ++  "]" else
          "|" ++ T.unpack x ++ "|"
