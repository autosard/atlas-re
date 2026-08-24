{-# LANGUAGE StrictData #-}

module CostAnalysis.Constraint
  ( Formula (..)
  , ArithExpr (..)
  , eq
  , ge
  , le
  , geZero
  , sum
  , minus
  , prod2
  , zero
  )where

import Prelude hiding (sum, or)

import CostAnalysis.Coeff

type Var = Int

data ArithExpr
  = VarTerm Var
  | CoeffTerm Coeff
  | Sum [ArithExpr]
  | Diff [ArithExpr]
  | Prod [ArithExpr]
  | Minus ArithExpr
  | ConstTerm Rational
  deriving (Eq, Ord, Show)

exprIsZero (ConstTerm 0) = True
exprIsZero _ = False

data Formula
  = Eq ArithExpr ArithExpr
  | Le ArithExpr ArithExpr
  | Ge ArithExpr ArithExpr
  | Impl Formula Formula
  | Iff Formula Formula
  | Not Formula
  | Or [Formula]
  | And [Formula]
  | Atom Var
  | Bot
  deriving (Eq, Ord, Show)

eq :: ArithExpr -> ArithExpr -> [Formula]
eq (ConstTerm x) (ConstTerm y) | x == y = []
eq t1 t2 = [Eq t1 t2]

sum :: [ArithExpr] -> ArithExpr
sum ts | all exprIsZero ts = ConstTerm 0
       | otherwise = sum' (filter (not. exprIsZero) ts)

sum' :: [ArithExpr] -> ArithExpr
sum' [t] = t
sum' ts = Sum ts

prod :: [ArithExpr] -> ArithExpr
prod ts | any exprIsZero ts = ConstTerm 0
       | otherwise = Prod ts

prod2 :: ArithExpr -> ArithExpr -> ArithExpr
prod2 t1 (ConstTerm 1) = t1
prod2 (ConstTerm 1) t2 = t2
prod2 t1 (ConstTerm (-1)) = minus t1
prod2 (ConstTerm (-1)) t2 = minus t2
prod2 t1 t2 = prod [t1, t2]

minus :: ArithExpr -> ArithExpr
minus = Minus

zero :: ArithExpr -> [Formula]
zero t = eq t (ConstTerm 0)

geZero :: ArithExpr -> [Formula]
geZero (ConstTerm 0) = []
geZero t = ge t (ConstTerm 0)

le :: ArithExpr -> ArithExpr -> [Formula]
le t1 t2 | t1 == t2 = []
le t1 t2 = [Le t1 t2]

ge :: ArithExpr -> ArithExpr -> [Formula]
ge t1 t2 | t1 == t2 = []
ge t1 t2 = [Ge t1 t2]

instance HasCoeffs ArithExpr where
  getCoeffs (CoeffTerm q) = [q]
  getCoeffs (Sum terms) = getCoeffs terms
  getCoeffs (Diff terms) = getCoeffs terms
  getCoeffs (Prod terms) = getCoeffs terms
  getCoeffs (Minus term) = getCoeffs term
  getCoeffs _ = []

instance HasCoeffs Formula where
  getCoeffs (Eq t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Le t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Ge t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Impl c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (Not c) = getCoeffs c
  getCoeffs (Or cs) = getCoeffs cs
  getCoeffs (And cs) = getCoeffs cs
  getCoeffs (Iff c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (Atom _) = []
  getCoeffs Bot = []
