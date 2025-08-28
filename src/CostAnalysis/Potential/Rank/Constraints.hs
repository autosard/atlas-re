{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Rank.Constraints where

import Prelude hiding (exp, (!!), sum, or)


import Primitive(Id)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le)
import CostAnalysis.Coeff
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential.Rank.Base(oneCoeff)
import Ast hiding (PotentialKind(..))
import qualified Data.Text as T
import CostAnalysis.Predicate (Predicate(..),
                               PredOp(..),
                               anyImplies)
import qualified CostAnalysis.Potential.Logarithm.Constraints as Log
import CostAnalysis.Annotation(Measure(..))
import Data.Set (Set)


exp :: Id
exp = "e1"

logArgs = Log.Args{
                 Log.leafRank=False,
                 Log.rankL=0,
                 Log.rankR=0,
                 Log.rankLR=0,
                 Log.rankOne=True}

constCases :: Pattern Positioned -> [Predicate]
constCases (ConstPat _ "leaf" _) = []
constCases p@(ConstPat _ "node" [Id _ t, _, Id _ u])
  = [Predicate Rank Le u t [] (getType p)]
    

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst e@(Leaf {}) _ (q, qe) q' = Log.cConst logArgs e q q'
cConst e@(Node (Var t) _ (Var u)) preds (q, qe) q'
  = let invariantCs = case anyImplies preds (Predicate Rank Le u t [] (getType e)) of
                        (True, cs) -> cs
                        (False, _) -> [Bot] in
    eq (q!?u) (q'!?exp)
    ++ eqSum (q!?oneCoeff) [q'!?exp, q'!?oneCoeff]
    ++ zero (q!?t)
    ++ Log.cConst logArgs e q q'
cConst (Ast.Const id _) _ (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch q p _ x [] = extend p $
  [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
  ++ Log.cMatch logArgs q x []
-- node
cMatch q r _ x xs@[u, v] = extend r $
  [
    (`eq` (q!x)) <$> def v
  ]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
  ++ Log.cMatch logArgs q x xs
cMatch _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti _ ps' x is r_ = extend r_
  [(`eq` (ps'!!i![mix|exp^d,e|])) <$> def i
  | i <- restrictFacs1 is,
    let d = facForVar i x,
    let e = max 0 $ constFactor i]

cLetCf :: FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf = Log.cLetCf
