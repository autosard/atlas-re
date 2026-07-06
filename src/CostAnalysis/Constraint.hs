{-# LANGUAGE StrictData #-}
{-# LANGUAGE PatternSynonyms #-}

module CostAnalysis.Constraint where

import Prelude hiding (sum, or)
import Data.List(intercalate)

import CostAnalysis.Coeff
import Control.Monad.State

type VarState = Int

type VarMonadT m a = StateT VarState m a

printVar :: Var -> String
printVar i = "k" ++ show i

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

sub :: [ArithExpr] -> ArithExpr
sub [t] = t
sub [t, ConstTerm 0] = t
sub ts | all exprIsZero ts = ConstTerm 0
       | otherwise = Diff ts

minus :: ArithExpr -> ArithExpr
minus = Minus

eqSum :: ArithExpr -> [ArithExpr] -> [Formula]
eqSum t ts = eq t $ sum ts

eqPlusMulti :: Coeff -> Coeff -> Coeff -> Var -> [Formula]
eqPlusMulti q p r k = eq (CoeffTerm q) $ Sum [CoeffTerm p, Prod [VarTerm k, CoeffTerm r]]

eqMulti :: Coeff -> Coeff -> Var -> [Formula]
eqMulti q p k = eq (CoeffTerm q) $ Prod [VarTerm k, CoeffTerm p]

zero :: ArithExpr -> [Formula]
zero t = eq t (ConstTerm 0)

geSum :: [ArithExpr] -> ArithExpr -> Formula
geSum ts = Ge (Sum ts)

notZero :: ArithExpr -> [Formula]
notZero t = Not <$> zero t

geZero :: ArithExpr -> [Formula]
geZero (ConstTerm 0) = []
geZero t = ge t (ConstTerm 0)

le :: ArithExpr -> ArithExpr -> [Formula]
le t1 t2 | t1 == t2 = []
le t1 t2 = [Le t1 t2]

ge :: ArithExpr -> ArithExpr -> [Formula]
ge t1 t2 | t1 == t2 = []
ge t1 t2 = [Ge t1 t2]


-- empty list corresponds to a true constraint
impl :: [Formula] -> [Formula] -> [Formula]
impl [] [] = []
impl [] [c2] = [c2]
impl [c1] [] = []
impl [c1] [c2] = [Impl c1 c2]
impl _ _ = error "cannot construct implication. "

iff :: [Formula] -> [Formula] -> [Formula]
iff [] [] = []
iff [c1] [c2] = [Iff c1 c2]

or :: [Formula] -> [Formula]
or [] = []
or cs = [Or cs]

or2 :: [Formula] -> [Formula] -> [Formula]
or2 [] _ = []
or2 _ [] = []
or2 xs ys = or (xs ++ ys)

and :: [Formula] -> [Formula]
and cs = [And cs]

printArithExpr :: ArithExpr -> String
printArithExpr (VarTerm k) = printVar k
printArithExpr (CoeffTerm q) = printCoeff q
printArithExpr (Sum terms) = printOpTerm "+" terms
printArithExpr (Diff terms) = printOpTerm "-" terms
printArithExpr (Prod terms) = printOpTerm "*" terms
printArithExpr (ConstTerm c) = show c

printOpTerm :: String -> [ArithExpr] -> String
printOpTerm op [] = "0"
printOpTerm op [t] = printArithExpr t
printOpTerm op terms = "(" ++ intercalate (" " ++ op ++ " ") (map printArithExpr terms) ++ ")"

printFormula :: Formula -> String
printFormula (Eq t1 t2) = printArithExpr t1 ++ " = " ++ printArithExpr t2
printFormula (Le t1 t2) = printArithExpr t1 ++ " <= " ++ printArithExpr t2
printFormula (Ge t1 t2) = printArithExpr t1 ++ " >= " ++ printArithExpr t2
printFormula (Impl c1 c2) = "(" ++ printFormula c1 ++ ") => (" ++ printFormula c2 ++ ")"
printFormula (Not c) = "not (" ++ printFormula c ++ ")"
printFormula (Or cs) = "or (" ++ intercalate "," (map printFormula cs) ++ ")"

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
