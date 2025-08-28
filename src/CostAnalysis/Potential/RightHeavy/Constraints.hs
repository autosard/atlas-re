{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.RightHeavy.Constraints where

import Prelude hiding (exp, (!!), sum, or, (^))
import qualified Data.List as L
import qualified Data.Set as S

import Primitive(Id, traceShow, traceShowV)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le, Lt)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.RightHeavy.Base(oneCoeff)
import qualified CostAnalysis.Potential.Logarithm.Constraints as Log
import Ast hiding (PotentialKind(..))
import CostAnalysis.Annotation(Measure(..))
import Data.List.Extra (groupSort)
import qualified Data.Text as T
import Data.Set (Set)
import CostAnalysis.Predicate (Predicate (Predicate), PredOp (..), anyImplies)


exp :: Id
exp = "e1"

logArgs = Log.Args{
                 Log.leafRank=False,
                 Log.rankL=0,
                 Log.rankR=0,
                 Log.rankLR=0,
                 Log.rankOne=False}

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst e@(Leaf {}) _ (q, _) q' =
  Log.cConst logArgs e q q'
  ++ concat [zero (q!idx)
            | idx <- mixes2 q]
cConst e@(Node (Var t) _ (Var u)) preds (q, qe) q' =
  let tLtU = [mix|t^(1,1),u^(2,1)|] in
    Log.cConst logArgs e q q'
    ++ eq (q!?t) (q'!?exp)
    ++ eq (q!?u) (q'!?exp)
    ++ eq (q!?tLtU) (q'!?exp)
    ++ concat [eq (q!idx) (q'!?[mix|_xs,exp^(a,b)|])
              | idx <- mixes2 q,
                let (a,b) = facForVar2 idx t,
                (a,b) == facForVar2 idx u,
                let xs = except idx [t,u]]
      
cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
cMatch q p _ x [] = extend p $
  [(`eq` (q!y)) <$> def y | y <- args q L.\\ [x,"!g1"]]
  ++ Log.cMatch logArgs q x []
  ++ [(`eqSum` qs) <$> def [mix|_xs, c|]
     | ((xs, c), qs) <- iverSums]
  where iverSums = groupSort $
                   [((xs, d), q!idx) 
                   | idx <- mixes2 q,
                     let (a,b) = facForVar2 idx x,
                     let c = constFactor idx,
                     let d = c + offset (a,b),
                     let xs = varsExcept idx [x]]
        offset (2,1) = -1
        offset (1,1) = 1
        offset (0,0) = 0

cMatch q r _ x xs@[t, u] = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u,
    (`eq` (q!x)) <$> def [mix|t^(1,1),u^(2,1)|]
  ]
  ++ Log.cMatch logArgs q x xs
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,t^(a,b),u^(a,b)|]
     | idx <- mixes2 q,
       let (a,b) = facForVar2 idx x,
       let xs = except idx [x]]

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti q ps' x is r_ = extend r_ $
  [(`eq` (ps'!!i![mix|exp^d,e|])) <$> def i
  | i <- restrictFacs1 is,
    let d = facForVar i x,
    let e = max 0 $ constFactor i]
  ++ [(`eq` (ps'!!i![mix|_lhs,exp^(1,1)|])) <$> def i
     | i <- restrictFacs2 is,
       let lhs = restrictFacsNoConst i [2,1]]
  ++ [(`eq` (q!i)) <$> def i
     | i <- mixes2 q,
       onlyVars i (args r_)]

cLetCf q _ps _ps' x (gamma, delta) bdes
  = let (ps, ps', _cs) = Log.cLetCf q _ps _ps' x (gamma, delta) bdes 
        (psDefined, psCs) = extends ps $
                            [eq (q!idx) . sum <$>
                              sequence [
                                 defEntry [mix|_rhs,_lhsDelta,lhsConst,x^(1,1)|] [mix|_rhs,_lhsGamma|],
                                 defEntry [mix|_rhs,_lhsDelta,x^(1,1)|] [mix|_rhs,_lhsGamma,lhsConst|]]
                            | idx <- mixes2 q,
                              let rhs = restrictFacsNoConst idx [2,1],
                              (not . null) rhs,
                              let rhsVars = varsForFac idx [2,1],
                              all (`elem` delta) rhsVars,

                              let lhs = restrictFacs idx [1,1],
                              let lhsDelta = varsRestrict (mixed lhs) delta,
                              let lhsGamma = varsRestrict (mixed lhs) gamma,
                              let lhsConst = constFactor (mixed lhs),
                              (not . null) lhsGamma]
        cs = concat [ zero (q!idx)
                    | idx <- mixes2 q,
                      let rhsVars = varsForFac idx [2,1],
                      any (`notElem` delta) rhsVars,
                      let lhsVars = varsForFac idx [1,1],
                      any (`elem` delta) lhsVars]
        (ps'Defined, ps'Cs) = extends ps' $
                              [[] <$ defEntry bde [mix|_lhs,exp^(1,1)|]
                              | bde <- restrictFacs2 bdes,
                                let ys = restrict bde delta,
                                let lhs = restrictFacsNoConst (mixed ys) [2,1]] in
        (psDefined, ps'Defined, _cs ++ psCs ++ ps'Cs ++ _cs ++ cs)

constCases :: Pattern Positioned -> [Predicate]
constCases _ = []
