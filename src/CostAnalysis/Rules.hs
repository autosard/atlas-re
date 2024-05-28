{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

data RuleArg = Mono | L2xy
  deriving (Eq, Show)

data Rule 
  = Leaf
  | Node
  | Cmp
  | Var
  | Pair
  | Ite 
  | Match 
  | Let 
  | App 
  | TickNow 
  | TickDefer 
  | Weaken [RuleArg] 
  | Shift 
  deriving(Eq, Show)

