{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.NLog.Base where

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

data Args = Args { }

nestedError = error "linear logarithmic potential only supports simple (non-nested) lists."

bearesPotential :: Type -> Bool
bearesPotential (TAp List [t]) | notNested t = True
                               | otherwise = nestedError
bearesPotential (TAp Tree [t]) | notNested t = True
                               | otherwise = nestedError                               
bearesPotential _ = False

ranges :: P.AnnRanges
ranges = P.AnnRanges [0..1] [0..2] [0..2]

rsrcAnn :: Int -> Text -> Text -> [(Id, Type)] -> ([Int], [Int]) -> RsrcAnn
rsrcAnn id label comment args ranges =
  RsrcAnn id args' label comment $ S.fromList coeffs
  where coeffs = defaultCoeffs vars ranges
        args' = filter (\(x, t) -> bearesPotential t) args
        vars = map fst args'

defaultCoeffs :: [Id] -> ([Int], [Int]) -> [CoeffIdx]
defaultCoeffs args (aRange, _) =
  [[mix|x^(a, b, c)|]
  | x <- args,
    a <- aRange,
    b <- aRange,
    c <- aRange,
    b + c <= 1]

               
constCoeff :: CoeffIdx
constCoeff = [mix||]

forAllCombinations :: Args -> RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
forAllCombinations potArgs q xs (rangeA, rangeB) x = filter (not . null . idxToSet ) $ varsRestrictMixes q xs

cExternal :: FunRsrcAnn -> [Constraint]
cExternal _ = []

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = error "pure coefficients are not supported with linear logarithmic potential."
printBasePot (Mixed factors) = printBasePot' $ S.toDescList factors

printBasePot' :: [Factor] -> String
printBasePot' [Arg x [a1, a2, a3]] = printA1 ++ printA2 ++ printA3
  where printIfPos a s = if a > 0 then s else ""
        printA1 = printIfPos a1 $ "|" ++ T.unpack x ++ "|"
        printA2 = printIfPos a2 $ " * log(|" ++ T.unpack x ++ "|)"
        printA3 = printIfPos a3 $ " * log(|" ++ T.unpack x ++ "| + 1" ++ ")"

 
