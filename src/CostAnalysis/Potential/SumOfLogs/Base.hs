{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.SumOfLogs.Base where

import Prelude hiding ((^))
import Data.List(intercalate)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.Template
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..), MonoFn(..))
import CostAnalysis.Constraint (Constraint, eq, Term(..))

-- c log(x + y) >= a log(x) + b log(y) + d
data LogLemmaCoeffs = LogLemmaCoeffs {
  llA :: !Rational,
  llB :: !Rational,
  llC :: !Rational,
  llD :: !Rational}
                                     

data Args = Args {
  aRange :: ![Int],
  bRange :: ![Int],
  logL :: !Rational,
  logR :: !Rational,
  logLR :: !Rational,
  logLemmaInstance :: !LogLemmaCoeffs}
  

potType = TreeType

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

template :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> FreeTemplate
template id label comment args ranges =
  FreeTemplate id args label comment $ S.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [Pure x | (x,i) <- zip args [1..]]
        logCoeffs = [idx
                    | idx <- combi ranges args,
                      idxSum idx > 0,
                      idx /= [mix|1|]]
               
oneCoeff :: CoeffIdx
oneCoeff = [mix|2|]

zeroCoeff :: Maybe CoeffIdx
zeroCoeff = Just [mix|1|]

monoFnCoeff :: MonoFn -> [Id] -> Int -> Maybe CoeffIdx
monoFnCoeff Log args c = let xs = S.fromList $ map (^1) args in
  Just [mix|_xs, c|]
monoFnCoeff _ args c = Nothing


cExternal :: FreeTemplate -> FreeTemplate -> [Constraint]
cExternal q q' = 
  -- equal ranks  
  concat [eq (q!?idx) t
  | idx <- pures q,
    let t = if M.member idx u then q'!?(u M.! idx) else ConstTerm 0]
  where u = apply q q'
    

letCfIdxs :: FreeTemplate -> [Id] -> ([Int], [Int]) -> Id -> [CoeffIdx] 
letCfIdxs q xs (rangeA, rangeB) x =
  [[mix|_bs,x^d,e|]
  | idx <- mixesForVars q xs,
    let bs = idxToSet idx,
    (not . null) bs,
    d <- rangeA,
    e <- rangeB,
    d + max e 0 > 0]

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "rk(" ++ T.unpack x ++ ")"
printBasePot (Mixed factors) = "log(" ++ intercalate " + " (map printFactor (S.toDescList factors)) ++ ")"
  where printFactor (Const c) = show c
        printFactor (Arg x [a]) = if a /= 1 then show a ++ "|" ++ T.unpack x ++ "|" else "|" ++ T.unpack x ++ "|"


