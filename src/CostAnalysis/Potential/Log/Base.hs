{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.Base where

import Prelude hiding ((^))
import Data.List(intercalate)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)

data Args = Args {
  aRange :: ![Int],
  bRange :: ![Int],
  dRange :: ![Int],
  eRange :: ![Int],
  eRangeNeg :: ![Int]}

types = [TreeType]

combi :: Args -> [Id] -> [Set Factor]
combi args xs = map S.fromList $
  combi' args [[Const c | c > 0] | c <- bRange args] xs

varCombi :: Args -> [Id] -> [Set Factor]
varCombi args xs = map S.fromList $ combi' args [[]] xs


combi' :: Args -> [[Factor]] -> [Id] -> [[Factor]]
combi' args z [] = z
combi' args z (x:xs) = [if a > 0 then x^a:y else y
                       | a <- aRange args, y <- combi' args z xs]

rsrcAnn :: Args
  -> Int -> Text -> [(Id, Type)] -> RsrcAnn
rsrcAnn potArgs id label args = RsrcAnn args' $ M.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [(Pure x, Coeff id label "log" (Pure x)) | (x,i) <- zip vars [1..]]
        logCoeffs = map ((\idx -> (idx, Coeff id label "log" idx)) . Mixed) $ combi potArgs vars
        args' = filter (\(x, t) -> matchesTypes t types) args
        vars = map fst args'

constCoeff :: RsrcAnn -> Coeff
constCoeff q = q![mix|2|]

forAllCombinations :: Args 
  -> Bool -> [(Id, Type)] -> Id -> Int -> Text -> [(Id, Type)] -> (AnnArray, Int)
forAllCombinations args neg xs x id label ys = (array, nextId)
  where trees = map fst $ filter (\(_, t) -> isTree t) xs
        idxs = [S.unions [xIdx, xsIdx, cIdx]
               | xIdx <- varCombi args [x], (not . S.null) xIdx,
                 xsIdx <- varCombi args trees, (not . S.null) xsIdx,
                 cIdx <- combi args []]
        nextId = id + length idxs
        arrIdx = Mixed . S.fromList
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' l idx = T.concat [l, "_", T.pack $ printIdx idx]
        array = M.fromList [(idx, rsrcAnn args id (label' label idx) ys)
                           | (idx, id) <- zip idxs [id..]]

printBasePot :: Coeff -> Rational -> String
printBasePot (Coeff _ _ _ (Pure x)) v = show v ++ " * rk(" ++ T.unpack x ++ ")"
printBasePot (Coeff _ _ _ (Mixed factors)) v = show v ++ " * " ++ printLog
  where printLog = "log(" ++ intercalate " + " (map printFactor (S.toDescList factors)) ++ ")"
        printFactor (Const c) = show c
        printFactor (Arg x a) = if a /= 1 then show a ++ T.unpack x else T.unpack x


