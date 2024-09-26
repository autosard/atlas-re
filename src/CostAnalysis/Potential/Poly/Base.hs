{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Poly.Base where

import Prelude hiding ((^))
import Data.Text(Text)
import qualified Data.Text as T
import Data.List(intercalate)
import qualified Data.Set as S

import Primitive(Id)
import Typing.Type
import qualified CostAnalysis.Potential as P
import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Constraint (Constraint)

data Args = Args { degree :: !Int }

types = [ListType]

notNested :: Type -> Bool
notNested (TAp List [t]) | isBase t = True
notNested (TAp Tree [t]) | isBase t = True
notNested _ = True

nestedError = error "Polynomial potential only supports simple (non-nested) inductive data types."

bearesPotential :: Type -> Bool
bearesPotential (TAp Prod ts) | all notNested ts = any bearesPotential ts
                              | otherwise = nestedError
bearesPotential (TAp List [t]) | notNested t = True
                               | otherwise = nestedError
bearesPotential _ = False

ranges :: Args -> P.AnnRanges
ranges potArgs = P.AnnRanges [0..degree potArgs] [] []


idxs :: Int -> Int -> [[Int]]
idxs _ 0 = return []
idxs d l = do
  nxt <- [0..d]
  (nxt :) <$> idxs (d - nxt) (l - 1) 

rsrcAnn :: Int -> Text -> Text -> [(Id, Type)] -> ([Int], [Int]) -> RsrcAnn
rsrcAnn id label comment args (degrees, _) =
  RsrcAnn id args' label comment $ S.fromList coeffs
  where coeffs = map (mixed . S.fromList . zipWith (^) vars)
          $ idxs (last degrees) (length vars)
        args' = filter (\(x, t) -> bearesPotential t) args
        vars = map fst args'
          
constCoeff :: CoeffIdx
constCoeff = [mix||]

forAllCombinations :: Args -> RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
forAllCombinations potArgs q xs (rangeA, rangeB) x = filter (not . null . idxToSet ) $ varsRestrictMixes q xs

cExternal :: FunRsrcAnn -> [Constraint]
cExternal _ = []

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = error "pure coefficients are not supported with polynomial potential."
printBasePot (Mixed factors) = concatMap printFactor (S.toDescList factors)
  where printFactor (Arg x a) = if a > 1 then
          "[" ++ T.unpack x ++ " " ++ show a ++  "]" else
          T.unpack x
