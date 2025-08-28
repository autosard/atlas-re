{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.SumOfLogs.Constraints where

import Prelude hiding (exp, (!!), sum, or)
import qualified Data.List as L
import qualified Data.Set as S
import Lens.Micro.Platform

import Primitive(Id)
import CostAnalysis.Template hiding (sum)
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.SumOfLogs.Base(Args(..),
                                             TreeInvariant(..),
                                             predFromInvariant)
import qualified CostAnalysis.Potential.Logarithm.Constraints as Log
import Data.List.Extra (groupSort)
import Ast
import qualified Data.Text as T
import CostAnalysis.Predicate (Predicate(..),
                               predApplySubst,
                               anyImplies)
import Data.Set (Set)
import Data.Maybe (maybeToList)


exp :: Id
exp = "e1"

logArgs :: Args -> Log.Args
logArgs (Args {logL=cL, logR=cR, logLR=cLR}) =
  Log.Args{
    Log.leafRank=True,
    Log.rankL=cL,
    Log.rankR=cR,
    Log.rankLR=cLR,
    Log.rankOne=False}

constCases :: Args -> Pattern Positioned -> [Predicate]
constCases _ (ConstPat _ "leaf" _) = []
constCases args p@(ConstPat _ "node" [Id _ t, _, Id _ u])
  = maybeToList (predFromInvariant args t u (getType p))

cConst :: Args -> PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst args e@(Leaf {}) _ (q, _) q' =
  Log.cConst (logArgs args) e q q' 
cConst args e@(Node (Var x1) _ (Var x2)) preds (q, qe) q'
    = let invariantCs = case predFromInvariant args x1 x2 (getType e) of
            Just p -> case anyImplies preds p of
              (True, cs) -> cs
              (False, _) -> [Bot]
            Nothing -> [] in
      eq (q!?x1) (q'!?exp) 
      ++ eq (q!?x2) (q'!?exp)
      ++ Log.cConst (logArgs args) e q q'
  
      
cMatch :: Args -> FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
cMatch pArgs q p _ x [] = extend p $
  [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
  ++ Log.cMatch (logArgs pArgs) q x []
cMatch pArgs q r _ x xs@[u, v] = extend r $
  [
    (`eq` (q!x)) <$> def u,
    (`eq` (q!x)) <$> def v]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
  ++ Log.cMatch (logArgs pArgs) q x xs
  
