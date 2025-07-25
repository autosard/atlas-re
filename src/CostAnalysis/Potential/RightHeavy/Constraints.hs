{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.RightHeavy.Constraints where

import Prelude hiding (exp, (!!), sum, or)


import Primitive(Id)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le, Lt)
import CostAnalysis.Coeff
import CostAnalysis.Potential.RightHeavy.Base(oneCoeff)
import Ast
import qualified Data.Text as T
import Data.Set (Set)
import CostAnalysis.Predicate (Predicate (Predicate), PredOp (..), anyImplies)
import Ast (Pattern)
import Data.Maybe (maybeToList)


exp :: Id
exp = "e1"

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst (Leaf {}) _ (q, qe) q' = eq (q!oneCoeff) (ConstTerm 0)
cConst (Node (Var t) _ (Var u)) preds (q, qe) q'
  = case anyImplies preds (Predicate "weight" Le u t Nothing) of
      (True, preCondition) ->
        eq (q!?t) (q'!?exp)
        ++ eq (q!?u) (q'!?exp)
        ++ preCondition
      (False, _) -> 
        eq (q!?t) (q'!?exp)
        ++ eq (q!?u) (q'!?exp)
        ++ eq (q!?oneCoeff) (q'!?exp)
  
cConst (Ast.Const id _) preds (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch q p _ x [] = extend p $
  ((`eq` (q!?oneCoeff)) <$> def oneCoeff)
  : [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
-- node
cMatch q r (Just (Predicate "weight" Lt x_ y_ _)) x [t, u]
  | x_ == t, y_ == u
  = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u,
    (`eqSum` [q!x,q!oneCoeff]) <$> def oneCoeff
  ]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
cMatch q r (Just (Predicate "weight" Le x_ y_ _)) x [t, u]
  | x_ == u, y_ == t
  = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u,
    (`eq` (q!oneCoeff)) <$> def oneCoeff
  ]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]  
cMatch _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

constCases :: Pattern Positioned -> [Predicate]
constCases (ConstPat _ "leaf" _) = []
constCases (ConstPat _ "node" [Id _ t, Id _ u])
  = [Predicate "weight" Lt t u Nothing,
     Predicate "weight" Le u t Nothing]

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti _ ps' x is r_ = extend r_ []

cLetCf :: FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf q ps ps' x (gamma, delta) bdes = error "undefined for univariate potential."
