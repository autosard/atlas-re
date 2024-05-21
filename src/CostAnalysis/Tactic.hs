{-# LANGUAGE StrictData #-}

module CostAnalysis.Tactic where

data RuleArg = Mono | L2xy
  deriving (Eq, Show)

data Tactic
  = Leaf
  | Node
  | Cmp
  | Var
  | Pair
  | Ite Tactic Tactic
  | Match [Tactic]
  | Let Tactic Tactic
  | App 
  | TickNow Tactic
  | TickDefer Tactic
  | Weaken [RuleArg] Tactic
  | Shift Tactic
  deriving (Eq, Show)
