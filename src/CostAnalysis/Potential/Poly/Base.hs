{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Poly.Base where

import Prelude hiding ((^))
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Set as S

import Primitive(Id)
import Typing.Type
import qualified CostAnalysis.Potential as P
import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Constraint (Constraint)

newtype Args = Args { degree :: Int }

types = [ListType]

nestedError = error "Polynomial potential only supports simple (non-nested) inductive data types."

ranges :: Args -> P.AnnRanges
ranges potArgs = P.AnnRanges [0..degree potArgs] [] []


idxs :: Int -> Int -> [[Int]]
idxs _ 0 = return []
idxs d l = do
  nxt <- [0..d]
  (nxt :) <$> idxs (d - nxt) (l - 1) 

rsrcAnn :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> RsrcAnn
rsrcAnn id label comment args (degrees, _) =
  RsrcAnn id args label comment $ S.fromList coeffs
  where coeffs = map (mixed . S.fromList . zipWith (^) args)
          $ idxs (last degrees) (length args)
          
oneCoeff :: CoeffIdx
oneCoeff = [mix||]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Nothing

forAllCombinations :: Args -> RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
forAllCombinations potArgs q xs (rangeA, rangeB) x = filter (not . null . idxToSet ) $ varsRestrictMixes q xs

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = error "pure coefficients are not supported with polynomial potential."
printBasePot (Mixed factors) = concatMap printFactor (S.toDescList factors)
  where printFactor (Arg x [a]) = if a > 1 then
          "[|" ++ T.unpack x ++ "| " ++ show a ++  "]" else
          "|" ++ T.unpack x ++ "|"
