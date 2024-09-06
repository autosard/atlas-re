{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.Base where

import Prelude hiding ((^))
import Data.List(intercalate)
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.RsrcAnn
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..))
import Constants

data Args = Args {
  aRange :: ![Int],
  bRange :: ![Int]}

types = [TreeType]

bearesPotential :: Type -> Bool
bearesPotential (TupleT x y) = if matchesTypes x types && matchesTypes y types
  then error "Tuples with two tree types are not supported."
  else matchesTypes x types /= matchesTypes y types
bearesPotential t = matchesTypes t types

ranges :: Args -> AnnRanges
ranges potArgs = AnnRanges (aRange potArgs) (bRange potArgs) (-1:bRange potArgs)

combi :: ([Int], [Int]) -> [Id] -> [CoeffIdx]
combi (rangeA, rangeB) xs = map (Mixed . S.fromList)$
  combi' rangeA [[Const c | c > 0] | c <- rangeB] xs

varCombi :: [Int] -> [Id] -> [CoeffIdx]
varCombi rangeA xs = map (Mixed . S.fromList) $ combi' rangeA [[]] xs

combi' :: [Int] -> [[Factor]] -> [Id] -> [[Factor]]
combi' _ z [] = z
combi' rangeA z (x:xs) = [if a > 0 then x^a:y else y
                       | a <- rangeA, y <- combi' rangeA z xs]

rsrcAnn :: Int -> Text -> Text -> [(Id, Type)] -> ([Int], [Int]) -> RsrcAnn
rsrcAnn id label comment args ranges =
  RsrcAnn id args' label comment $ S.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [Pure x | (x,i) <- zip vars [1..]]
        logCoeffs = [idx
                    | idx <- combi ranges vars,
                      idxSum idx > 0,
                      idx /= [mix|1|]]
        args' = filter (\(x, t) -> bearesPotential t) args
        vars = map fst args'

               
constCoeff :: CoeffIdx
constCoeff = [mix|2|]

printBasePot :: Coeff -> Rational -> String
printBasePot (Coeff _ _ _ (Pure x)) v = show v ++ " * rk(" ++ T.unpack x ++ ")"
printBasePot (Coeff _ _ _ (Mixed factors)) v = show v ++ " * " ++ printLog
  where printLog = "log(" ++ intercalate " + " (map printFactor (S.toDescList factors)) ++ ")"
        printFactor (Const c) = show c
        printFactor (Arg x a) = if a /= 1 then show a ++ T.unpack x else T.unpack x


