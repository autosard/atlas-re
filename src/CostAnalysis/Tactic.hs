{-# LANGUAGE StrictData #-}

module CostAnalysis.Tactic where

import CostAnalysis.Rules

data Tactic
  = Rule Rule [Tactic]
  | Hole
  | Auto
  deriving (Eq, Show)

subTactics :: Int -> Tactic -> [Tactic]
subTactics _ (Rule _ subs) = subs
subTactics n Auto = replicate n Auto
subTactics n Hole = replicate n Hole

printTacticHead :: Tactic -> String
printTacticHead (Rule r _) = "(" ++ show r ++ " ...)"
printTacticHead t = show t
