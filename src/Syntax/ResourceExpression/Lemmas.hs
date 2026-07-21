{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Syntax.ResourceExpression.Lemmas where

import Data.Ratio ((%))
import Syntax.ResourceExpression.Pattern


data WeightedPattern = WeightedPattern Rational TermPattern

data LemmaSpec = LemmaSpec
  { lemmaPatterns :: [WeightedPattern]
  , constantShift :: Rational
  }

logLemmaSpec :: LemmaSpec
logLemmaSpec = LemmaSpec
  { lemmaPatterns = 
      [ WeightedPattern (1%2) (PGenLog [SizeVar "x"])
      , WeightedPattern (1%2) (PGenLog [SizeVar "y"])
      , WeightedPattern (- 1) (PGenLog [SizeVar "x", SizeVar "y"])
      ]
  , constantShift = 1
  }
