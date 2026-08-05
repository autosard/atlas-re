{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.Rules where

import Lens.Micro.Platform

import Syntax.Ast
import CostAnalysis.Constraint
import CostAnalysis.Template

data JudgementType = Standard | CfEq | Cf
  deriving (Eq, Ord, Show)

data SubArg = Mono | L2xy 
  deriving (Eq, Ord, Show)

-- data LetArg = NegE
--   deriving (Eq, Ord, Show)

data Rule 
  = Const
  | Var
  | Ite
  | IteCoin
  | Match 
  | Let 
  | App 
  | Tick
  | Sub [SubArg]
  | Shift
  | Lit
  deriving(Eq, Show)

data RuleAppInfo = RuleAppInfo {
  _raJt :: JudgementType
  , _raQ :: FreeTemplate
  , _raQ' :: FreeTemplate
  , _raCs :: [Formula]
  , _raExpr :: PositionedExpr
  } deriving Show

makeLenses ''RuleAppInfo

data RuleApp 
  = ExprRuleApp Rule RuleAppInfo
  | MatchArmApp (Pattern Positioned) RuleAppInfo
  | FunRuleApp (FunDef Positioned)
  deriving Show

