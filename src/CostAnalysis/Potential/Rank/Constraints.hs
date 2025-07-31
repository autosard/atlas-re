{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Rank.Constraints where

import Prelude hiding (exp, (!!), sum, or)


import Primitive(Id)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le)
import CostAnalysis.Coeff
import CostAnalysis.Potential.Rank.Base(oneCoeff)
import Ast hiding (PotentialKind(..))
import qualified Data.Text as T
import CostAnalysis.Predicate (Predicate(..), PredOp(..))
import CostAnalysis.Annotation(Measure(..))
import Data.Set (Set)


exp :: Id
exp = "e1"

constCases :: Pattern Positioned -> [Predicate]
constCases (ConstPat _ "leaf" _) = []
constCases p@(ConstPat _ "node" [Id _ t, _, Id _ u])
  = [Predicate Rank Le u t [] (getType p)]
    

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst (Leaf {}) _ (q, qe) q' = eq (q!oneCoeff) (q'!?oneCoeff)
cConst e@(Node (Var x1) _ (Var x2)) _ (q, qe) q'
  = eq (q!?x2) (sub [q'!?exp, qe!?exp])
    ++ eqSum (q!?oneCoeff) [sub [q'!?exp, qe!?exp], q'!oneCoeff]
    ++ zero (q!?x1)
cConst (Ast.Const id _) _ (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch q p _ x [] = extend p $
  ((`eq` (q!?oneCoeff)) <$> def oneCoeff)
  : [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
-- node
cMatch q r _ x [u, v] = extend r $
  [
    (`eq` (q!x)) <$> def v,
    (`eqSum` [q!x,q!oneCoeff]) <$> def oneCoeff
  ]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
cMatch _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti _ ps' x is r_ = extend r_ []

cLetCf :: FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf q ps ps' x (gamma, delta) bdes = error "undefined for univariate potential."
