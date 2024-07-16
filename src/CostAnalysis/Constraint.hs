{-# LANGUAGE StrictData #-}

module CostAnalysis.Constraint where

import Data.List(intercalate)

import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn 

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
  -- | 'GeSum' ps q = \[\sum^N_{i=1} p_i \geq q\]
  | GeSum [Coeff] Coeff
  -- | 'GeImpl' c1 c2 = \[C_1 \Rightarrow C_2 \]
  | Impl Constraint Constraint
  -- | @'EqSub' q ps@ = \[q = p_1 - \dots - p_n\]
  | EqSub Coeff [Coeff]
  -- | @'EqMultConst' q p c@ = \[q = c \cdot p\]
  | EqMultConst Coeff Coeff Rational
  -- | @'Minimize' q@ minimize coefficient @q@
  | Minimize Coeff
  deriving (Eq, Ord, Show)

printSum :: [Coeff] -> String
printSum qs = "(" ++ intercalate " + " (map printCoeff qs) ++ ")"

printDiff :: [Coeff] -> String
printDiff qs = "(" ++ intercalate " - " (map printCoeff qs) ++ ")"

printConstraint :: Constraint -> String
printConstraint (Eq q p) = printCoeff q ++ " = " ++ printCoeff p
printConstraint (EqSum q ps) = printCoeff q ++ " = " ++ printSum ps
printConstraint (EqPlusConst q p c) = printCoeff q ++ " = " ++ printCoeff p ++ " + " ++ show c
printConstraint (EqMinusConst q p c) = printCoeff q ++ " = " ++ printCoeff p ++ " - " ++ show c
printConstraint (EqMinusVar q p) = printCoeff q ++ " = " ++ printCoeff p ++ " - k"
printConstraint (EqPlusMulti q p r) = printCoeff q ++ " = " ++ printCoeff p ++ " + k *" ++ printCoeff r
printConstraint (Zero q) = printCoeff q ++ " = 0"
printConstraint (NotZero q) = printCoeff q ++ " /= 0"
printConstraint (Le q p) = printCoeff q ++ " <= " ++ printCoeff p
printConstraint (GeSum ps q) = printSum ps ++ " >= " ++ printCoeff q
printConstraint (Impl c1 c2) = printConstraint c1 ++ " -> " ++ printConstraint c2
printConstraint (EqSub q ps) = printCoeff q ++ " = " ++ printDiff ps
printConstraint (EqMultConst q p c) = printCoeff q ++ " = c * " ++ printCoeff p
printConstraint (Minimize q) = "min(" ++ printCoeff q ++ ")"

instance HasCoeffs Constraint where
  getCoeffs (Eq q p) = [q, p]
  getCoeffs (EqSum q qs) = q:qs
  getCoeffs (EqPlusConst q p _) = [q,p]
  getCoeffs (EqMinusConst q p _) = [q,p]
  getCoeffs (EqMinusVar q p) = [q,p]
  getCoeffs (EqPlusMulti q p r) = [q,p,r]
  getCoeffs (Zero q) = [q]
  getCoeffs (NotZero q) = [q]
  getCoeffs (Le q p) = [q,p]
  getCoeffs (GeSum qs p) = p:qs
  getCoeffs (Impl c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (EqSub q ps) = q:ps
  getCoeffs (EqMultConst q p _) = [q,p]
  getCoeffs (Minimize q) = [q]
  

