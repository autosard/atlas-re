{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.TreeSize.Constraints where

import Prelude hiding (exp, (!!), sum, or)


import Primitive(Id)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le, Lt)
import CostAnalysis.Coeff
import CostAnalysis.Potential.TreeSize.Base(oneCoeff)
import qualified Data.Text as T
import Data.Set (Set)
import CostAnalysis.Predicate (Predicate (Predicate), PredOp (..), anyImplies)
import Ast 


exp :: Id
exp = "e1"

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst (Leaf {}) _ (q, qe) q' = eq (q!oneCoeff) (q'!exp)
cConst (Node (Var t) _ (Var u)) _ (q, qe) q'
  = eq (q!?t) (q'!?exp)
    ++ eq (q!?u) (q'!?exp)
cConst (Ast.Const id _) preds (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch q p _ x [] = extend p $
  ((`eqSum` [q!?oneCoeff, q!?x]) <$> def oneCoeff)
  : [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
-- node
cMatch q r _ x [t, u]
  = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u,
    (`eq` (q!oneCoeff)) <$> def oneCoeff
  ]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
cMatch _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

constCases :: Pattern Positioned -> [Predicate]
constCases _ = []

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti _ ps' x is r_ = extend r_ []

cLetCf :: FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf q ps ps' x (gamma, delta) bdes = error "undefined for univariate potential."
