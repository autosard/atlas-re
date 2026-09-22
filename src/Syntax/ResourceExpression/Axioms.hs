{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Syntax.ResourceExpression.Axioms
  ( AxiomSpec (..)
  , WeightedPattern (..)
  , logAxiom
  ) where

import Data.Ratio ((%))
import Syntax.ResourceExpression.Pattern
import qualified Syntax.FreeModule as FM


data WeightedPattern = WeightedPattern Rational TermPattern

data AxiomSpec = AxiomSpec
  { premises :: [IneqPattern]
  , conclusion :: IneqPattern
  }
  deriving (Eq, Show)

logAxiom :: AxiomSpec
logAxiom = AxiomSpec
  { premises = []
  , conclusion = LeZero $ FM.fromList'
      [ (TPLog $ FM.singleton (SPVar "x"), 1%2)
      , (TPLog $ FM.singleton (SPVar "y"), 1%2)
      , (TPLog $ FM.fromList [SPVar "x", SPVar "y"], - 1)
      , (TPId , 1)
      ]
  }
