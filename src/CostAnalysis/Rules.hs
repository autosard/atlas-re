{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

import CostAnalysis.Constraint
import CostAnalysis.Annotation
import CostAnalysis.Predicate
import Ast
import Data.Text(unpack)
import Data.Set(Set)

data WeakenArg = Mono | L2xy | Neg
  deriving (Eq, Ord, Show)

data LetArg = NegE
  deriving (Eq, Ord, Show)

data Rule 
  = Const
  | ConstBase
  | ConstUnfold
  | Var
  | Ite 
  | Match 
  | Let [LetArg]
  | App 
  | TickNow 
  | TickDefer
  | WeakenVar
  | Weaken [WeakenArg]
  | ShiftConst
  | ShiftTerm
  deriving(Eq, Show)

data RuleApp
  = ExprRuleApp
    Rule
    Bool
    ProveKind
    (FreeAnn, FreeAnn, Set Predicate)
    FreeAnn
    [Constraint]
    PositionedExpr
  | FunRuleApp PositionedFunDef
  | ProgRuleApp PositionedModule
  deriving Show

{-# DEPRECATED #-}          
printRuleApp _ _ (FunRuleApp (Fn name _ _)) = "Fun: " ++ unpack name
printRuleApp _ _ (ProgRuleApp _) = "Prog" 
