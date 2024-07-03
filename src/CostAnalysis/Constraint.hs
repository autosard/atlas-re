{-# LANGUAGE StrictData #-}

module CostAnalysis.Constraint where

import CostAnalysis.Coeff

data Constraint =
  -- | 'Eq' q p = \[q = p\]
  Eq Coeff Coeff 
  -- | 'EqSum' q ps = \[q = \sum^N_{i=1} p_i \]
  | EqSum Coeff [Coeff]
  -- | 'EqPlusConst' q p c = \[q = p + c \]
  | EqPlusConst Coeff Coeff Rational
  -- | 'EqMinusConst' q p c = \[q = p - c \]
  | EqMinusConst Coeff Coeff Rational
  -- | 'EqMinusVar' q p = \[q = p - k \]
  | EqMinusVar Coeff Coeff
  -- | 'EqPlusMulti' q p r = \[ q = p + k r\]
  | EqPlusMulti Coeff Coeff Coeff
  -- | 'Zero' q = \[q = 0 \]
  | Zero Coeff
  -- | 'NotZero' q = \[q \neq 0 \]
  | NotZero Coeff
  -- | 'Le' q p = \[q \leq p \]
  | Le Coeff Coeff
  -- | 'GeSum' q ps = \[q \geq \sum^N_{i=1} p_i \]
  | GeSum [Coeff] Coeff
  -- | 'GeSum' c1 c2 = \[C_1 \Rightarrow C_2 \]
  | Impl Constraint Constraint
  -- | @'EqSub' q ps@ = \[q = p_1 - \dots - p_n\]
  | EqSub Coeff [Coeff]
  -- | @'EqMultConst' q p c@ = \[q = c \cdot p\]
  | EqMultConst Coeff Coeff Rational
  -- | @'Minimize' q@ minimize coefficient @q@
  | Minimize Coeff
  deriving (Eq, Ord, Show)
