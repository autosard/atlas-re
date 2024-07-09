{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

data RuleArg = Mono | L2xy
  deriving (Eq, Show)

data Rule 
  = Const
  | Cmp
  | Var
  | Ite 
  | Match 
  | Let 
  | App 
  | TickNow 
  | TickDefer
  | WeakenVar
  | Weaken [RuleArg]
  | Shift 
  deriving(Eq, Show)

