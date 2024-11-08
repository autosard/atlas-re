{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.NLog.Base where

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

rsrcAnn :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> RsrcAnn
rsrcAnn id label comment args ranges =
  RsrcAnn id args label comment $ S.fromList coeffs
  where coeffs = defaultCoeffs args ranges

defaultCoeffs :: [Id] -> ([Int], [Int]) -> [CoeffIdx]
defaultCoeffs args (aRange, bRange) =
  [[mix|x^(a, b), c|]
  | x <- args,
    a <- aRange,
    b <- aRange,
    c <- bRange,
    b + c <= 2,
    b + c > 0,
    not (a == 1 && b == 0 &&  c == 1)]

               
oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Just [mix|1|]
  
forAllCombinations :: Args -> RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
forAllCombinations potArgs q xs (rangeA, rangeB) x = filter (not . null . idxToSet ) $ varsRestrictMixes q xs

cExternal :: RsrcAnn -> RsrcAnn -> [Constraint]
cExternal _ _ = []

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = error "pure coefficients are not supported with linear logarithmic potential."
printBasePot idx = 
  let [x] = coeffArgs idx
      (a, b) = facForVar2 idx x
      c = constFactor idx in
    printN a x ++ printLogN b x c
  where printIfPos a s = if a > 0 then s else ""
        printN a x = printIfPos a $ "|" ++ T.unpack x ++ "|"
        printLogN b x c = printIfPos b $ " * log(" ++ printIfPos b ("|" ++ T.unpack x ++ "|") ++ printIfPos c (show c) ++ ")"

--printBasePot' :: [Factor] -> String
--printBasePot' [Arg x [a, b], Const c] = 
--printBasePot' fs = error $ "non exaustive pattern: " ++ show fs
    

 
