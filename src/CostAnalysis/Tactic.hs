{-# LANGUAGE StrictData #-}

module CostAnalysis.Tactic where

import CostAnalysis.Rules

data Tactic
  = Rule Rule [Tactic]
  | Hole
  | Auto
  deriving (Eq, Show)
