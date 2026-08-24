{-# LANGUAGE StrictData #-}

module CostAnalysis.Tactic
  ( Tactic (..)
  , subTactics
  )where

import CostAnalysis.Rules
import Syntax.PrettyPrint 

data Tactic
  = Rule Rule [Tactic]
  | Hole
  | Auto
  deriving (Eq, Show)

subTactics :: Int -> Tactic -> [Tactic]
subTactics _ (Rule _ subs) = subs
subTactics n Auto = replicate n Auto
subTactics n Hole = replicate n Hole

instance PrettyPrint Tactic where
  prettyPrint (Rule r _) = "(" ++ show r ++ " ...)"
  prettyPrint t = show t
