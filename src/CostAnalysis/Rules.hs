{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.Rules
  ( Rule (..)
  , JudgementType (..)
  , RuleAppInfo (..)
  , RuleApp (..)
  , SubArg (..)
  )where

import Lens.Micro.Platform

import Syntax (Positioned)
import Syntax.Expression (Expr)
import Syntax.Pattern (Pattern)
import Syntax.Program
import CostAnalysis.Constraint
import CostAnalysis.Template

data JudgementType = Standard | CfEq | Cf
  deriving (Eq, Ord, Show)

data SubArg = Mono | L2xy 
  deriving (Eq, Ord, Show)

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
  , _raExpr :: Expr Positioned
  } deriving Show

makeLenses ''RuleAppInfo

data RuleApp 
  = ExprRuleApp Rule RuleAppInfo
  | MatchArmApp (Pattern Positioned) RuleAppInfo
  | FunRuleApp (FunDef Positioned)
  deriving Show

