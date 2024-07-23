{-# LANGUAGE StrictData #-}

module CostAnalysis.Constraint where

import Data.List(intercalate)

import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn 
import Control.Monad.State

type VarState = Int

type VarMonadT m a = StateT VarState m a

data Var = Var Bool Int | AnnCoeff Coeff
  deriving (Eq, Ord, Show)

printVar (Var pos i) = "k" ++ (if pos then "+" else "") ++ show i
printVar (AnnCoeff coeff) = printCoeff coeff

data Constraint =
  -- | 'Eq' q p = \[q = p\]
  Eq Var Var 
  -- | 'EqSum' q ps = \[q = \sum^N_{i=1} p_i \]
  | EqSum Var [Var]
  -- | 'EqPlusConst' q p c = \[q = p + c \]
  | EqPlusConst Var Var Rational
  -- | 'EqMinusConst' q p c = \[q = p - c \]
  | EqMinusConst Var Var Rational
  -- | 'EqMinusVar' q p k = \[q = p - k \]
  | EqMinusVar Var Var Var
  -- | 'EqPlusMulti' q p r k = \[ q = p + k r\]
  | EqPlusMulti Var Var Var Var
  -- | 'EqPlusMulti' q p k = \[ q = k p\]
  | EqMulti Var Var Var 
  -- | 'Zero' q = \[q = 0 \]
  | Zero Var
  -- | 'NotZero' q = \[q \neq 0 \]
  | NotZero Var
  -- | 'Le' q p = \[q \leq p \]
  | Le Var Var
  -- | 'GeSum' ps q = \[\sum^N_{i=1} p_i \geq q\]
  | GeSum [Var] Var
  -- | 'GeImpl' c1 c2 = \[C_1 \Rightarrow C_2 \]
  | Impl Constraint Constraint
  -- | @'EqSub' q ps@ = \[q = p_1 - \dots - p_n\]
  | EqSub Var [Var]
  -- | @'EqMultConst' q p c@ = \[q = c \cdot p\]
  | EqMultConst Var Var Rational
  -- | @'FarkasA p fas q'@ = \[p \leq f_1 \cdot a_1 + \dots + f_n \cdot a_n + q\]
  | FarkasA Coeff [(Var, Int)] Coeff
  -- | @'FarkasB fbs cP cQ'@ = \[ f_1 \cdot b_1 + \dots + f_n \cdot b_n \leq 0 \]
  | FarkasB [(Var, Int)] 
  -- | @'Minimize' q@ minimize coefficient @q@
  | Minimize Var
  deriving (Eq, Ord, Show)

eq :: Coeff -> Coeff -> Constraint
eq q p = Eq (AnnCoeff q) (AnnCoeff p)

eqSum :: Coeff -> [Coeff] -> Constraint
eqSum q ps = EqSum (AnnCoeff q) (map AnnCoeff ps)

eqPlusConst :: Coeff -> Coeff -> Rational -> Constraint
eqPlusConst q p = EqPlusConst (AnnCoeff q) (AnnCoeff p)

eqMinusVar :: Coeff -> Coeff -> Var -> Constraint
eqMinusVar q p = EqMinusVar (AnnCoeff q) (AnnCoeff p)

eqPlusMulti :: Coeff -> Coeff -> Coeff -> Var -> Constraint
eqPlusMulti q p r = EqPlusMulti (AnnCoeff q) (AnnCoeff p) (AnnCoeff r)

eqMulti :: Coeff -> Coeff -> Var -> Constraint
eqMulti q p = EqMulti (AnnCoeff q) (AnnCoeff p)

zero :: Coeff -> Constraint
zero q = Zero (AnnCoeff q)

geSum :: [Coeff] -> Coeff -> Constraint
geSum ps q = GeSum (map AnnCoeff ps) (AnnCoeff q)

notZero :: Coeff -> Constraint
notZero q = NotZero (AnnCoeff q)

le :: Coeff -> Coeff -> Constraint
le q p = Le (AnnCoeff q) (AnnCoeff p)

printSum :: [Var] -> String
printSum qs = "(" ++ intercalate " + " (map printVar qs) ++ ")"

printProdSum :: [(Var, Int)] -> String
printProdSum qs = "(" ++ intercalate " + " (map (\(v, c) -> show c ++ " * " ++ printVar v) qs) ++ ")"

printDiff :: [Var] -> String
printDiff qs = "(" ++ intercalate " - " (map printVar qs) ++ ")"

printConstraint :: Constraint -> String
printConstraint (Eq q p) = printVar q ++ " = " ++ printVar p
printConstraint (EqSum q ps) = printVar q ++ " = " ++ printSum ps
printConstraint (EqPlusConst q p c) = printVar q ++ " = " ++ printVar p ++ " + " ++ show c
printConstraint (EqMinusConst q p c) = printVar q ++ " = " ++ printVar p ++ " - " ++ show c
printConstraint (EqMinusVar q p k) = printVar q ++ " = " ++ printVar p ++ " - " ++ printVar k
printConstraint (EqPlusMulti q p r k) = printVar q ++ " = " ++ printVar p ++ " + " ++ printVar k++ " *" ++ printVar r
printConstraint (EqMulti q p k) = printVar q ++ " = " ++ printVar k ++ " *" ++ printVar p
printConstraint (Zero q) = printVar q ++ " = 0"
printConstraint (NotZero q) = printVar q ++ " /= 0"
printConstraint (Le q p) = printVar q ++ " <= " ++ printVar p
printConstraint (GeSum ps q) = printSum ps ++ " >= " ++ printVar q
printConstraint (Impl c1 c2) = printConstraint c1 ++ " -> " ++ printConstraint c2
printConstraint (EqSub q ps) = printVar q ++ " = " ++ printDiff ps
printConstraint (EqMultConst q p c) = printVar q ++ " = c * " ++ printVar p
printConstraint (Minimize q) = "min(" ++ printVar q ++ ")"
printConstraint (FarkasA p fas q) = printCoeff p ++ " <= " ++ printProdSum fas ++ " + " ++ printCoeff q

instance HasCoeffs Var where
  getCoeffs (AnnCoeff coeff) = [coeff]
  getCoeffs _ = []

instance HasCoeffs Constraint where
  getCoeffs (Eq q p) = getCoeffs q ++ getCoeffs p
  getCoeffs (EqSum q qs) = getCoeffs q ++ getCoeffs qs
  getCoeffs (EqPlusConst q p _) = getCoeffs q ++ getCoeffs p
  getCoeffs (EqMinusConst q p _) = getCoeffs q ++ getCoeffs p
  getCoeffs (EqMinusVar q p _) = getCoeffs q ++ getCoeffs p
  getCoeffs (EqPlusMulti q p r k) = getCoeffs q ++ getCoeffs p ++ getCoeffs r
  getCoeffs (EqMulti q p k) = getCoeffs q ++ getCoeffs p
  getCoeffs (Zero q) = getCoeffs q
  getCoeffs (NotZero q) = getCoeffs q
  getCoeffs (Le q p) = getCoeffs q ++ getCoeffs p
  getCoeffs (GeSum qs p) = getCoeffs p ++ getCoeffs qs
  getCoeffs (Impl c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (EqSub q ps) = getCoeffs q ++ getCoeffs ps
  getCoeffs (EqMultConst q p _) = getCoeffs q ++ getCoeffs p
  getCoeffs (FarkasA q _ p) = [q, p]
  getCoeffs (FarkasB _) = []
  getCoeffs (Minimize q) = getCoeffs q
  

