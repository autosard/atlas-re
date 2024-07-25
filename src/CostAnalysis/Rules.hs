{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

data WeakenArg = Mono | L2xy
  deriving (Eq, Ord, Show)

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
  | Weaken [WeakenArg]
  | Shift
  deriving(Eq, Show)

