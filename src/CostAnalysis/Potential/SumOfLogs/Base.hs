{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.SumOfLogs.Base where

import Prelude hiding ((^))
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.Coeff

import CostAnalysis.Template
import Typing.Type
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential (AnnRanges(..), MonoFn(..), JudgementType(..))
import CostAnalysis.Potential.Logarithm.Base
import CostAnalysis.Constraint (Constraint, eq, Term(..))
import CostAnalysis.Predicate (PredOp, Predicate(..))
import CostAnalysis.Annotation(Measure)
import Ast (getType)

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
  logLemmaInstance :: !LogLemmaCoeffs,
  invariant :: !(Maybe TreeInvariant)}

data TreeInvariant = TreeInvariant Measure PredOp Bool

predFromInvariant :: Args -> Id -> Id -> Type -> Maybe Predicate
predFromInvariant args x y t = case invariant args of
      Just (TreeInvariant m op flip) -> if flip
        then Just $ Predicate m op y x [] t
        else Just $ Predicate m op x y [] t
      Nothing -> Nothing

potType = TreeType

ranges :: Args -> AnnRanges
ranges potArgs = AnnRanges (aRange potArgs) (bRange potArgs) (-1:bRange potArgs)

template :: Int -> Text -> Text -> [Id] -> ([Int], [Int]) -> FreeTemplate
template id label comment args ranges =
  FreeTemplate id args label comment $ S.fromList (rankCoeffs ++ logCoeffs args ranges)
  where rankCoeffs = [Pure x | (x,i) <- zip args [1..]]
               
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
    

letCfIdxs :: FreeTemplate -> [Id] -> ([Int], [Int]) -> Id -> [(JudgementType, CoeffIdx)] 
letCfIdxs q xs (rangeA, rangeB) x =
  [(Cf 0, [mix|_bs,x^d,e|])
  | idx <- mixesForVars q xs,
    let bs = idxToSet idx,
    (not . null) bs,
    d <- rangeA,
    e <- rangeB,
    d + max e 0 > 0]

printBasePot :: CoeffIdx -> String
printBasePot (Pure x) = "rk(" ++ T.unpack x ++ ")"
printBasePot idx = printLogTerm idx


