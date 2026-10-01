{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Syntax.ResourceExpression.Axioms
  ( AxiomSpec (..)
  , WeightedPattern (..)
  ) where

import Syntax.ResourceExpression.Pattern

data WeightedPattern = WeightedPattern Rational TermPattern

data AxiomSpec = AxiomSpec
  { premises :: [IneqPattern]
  , conclusion :: IneqPattern
  }
  deriving (Eq, Show)
