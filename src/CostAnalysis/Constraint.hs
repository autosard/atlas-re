{-# LANGUAGE StrictData #-}
{-# LANGUAGE PatternSynonyms #-}

module CostAnalysis.Constraint where

import Data.List(intercalate)

import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn 
import Control.Monad.State

type VarState = Int

type VarMonadT m a = StateT VarState m a

printVar :: Var -> String
printVar i = "k" ++ show i

type Var = Int

data Term
  = VarTerm Var
  | CoeffTerm Coeff
  | Sum [Term]
  | Diff [Term]
  | Prod [Term]
  | ConstTerm Rational
  deriving (Eq, Ord, Show)

data Constraint
  = Eq Term Term
  | Zero Term
  | Le Term Term
  | Ge Term Term
  | Impl Constraint Constraint
  | Not Constraint
  deriving (Eq, Ord, Show)

pattern Prod2 :: Term -> Term -> Term 
pattern Prod2 t1 t2 <- Prod [t1, t2]
  where Prod2 t1 t2 = Prod [t1, t2]

eq :: Coeff -> Coeff -> Constraint
eq q p = Eq (CoeffTerm q) (CoeffTerm p)

sub :: [Coeff] -> Term
sub qs = Diff (map CoeffTerm qs)

eqSum :: Coeff -> [Coeff] -> Constraint
eqSum q ps = Eq (CoeffTerm q) $ Sum (map CoeffTerm ps)

eqPlusConst :: Coeff -> Coeff -> Rational -> Constraint
eqPlusConst q p k = Eq (CoeffTerm q) $ Sum [CoeffTerm p, ConstTerm k]

eqMinusVar :: Coeff -> Coeff -> Var -> Constraint
eqMinusVar q p k = Eq (CoeffTerm q) $ Diff [CoeffTerm p, VarTerm k]

eqPlusMulti :: Coeff -> Coeff -> Coeff -> Var -> Constraint
eqPlusMulti q p r k = Eq (CoeffTerm q) $ Sum [CoeffTerm p, Prod [VarTerm k, CoeffTerm r]]

eqMulti :: Coeff -> Coeff -> Var -> Constraint
eqMulti q p k = Eq (CoeffTerm q) $ Prod [VarTerm k, CoeffTerm p]

zero :: Coeff -> Constraint
zero q = Zero (CoeffTerm q)

geSum :: [Coeff] -> Coeff -> Constraint
geSum ps q = Ge (Sum (map CoeffTerm ps)) (CoeffTerm q)

notZero :: Coeff -> Constraint
notZero q = Not $ Zero (CoeffTerm q)

varGeZero :: Var -> Constraint
varGeZero x = Ge (VarTerm x) (ConstTerm 0)

le :: Coeff -> Coeff -> Constraint
le q p = Le (CoeffTerm q) (CoeffTerm p)

printTerm :: Term -> String
printTerm (VarTerm k) = printVar k
printTerm (CoeffTerm q) = printCoeff q
printTerm (Sum terms) = printOpTerm "+" terms
printTerm (Diff terms) = printOpTerm "-" terms
printTerm (Prod terms) = printOpTerm "*" terms
printTerm (ConstTerm c) = show c

printOpTerm :: String -> [Term] -> String
printOpTerm op [] = "0"
printOpTerm op [t] = printTerm t
printOpTerm op terms = "(" ++ intercalate (" " ++ op ++ " ") (map printTerm terms) ++ ")"

printConstraint :: Constraint -> String
printConstraint (Eq t1 t2) = printTerm t1 ++ " = " ++ printTerm t2
printConstraint (Zero t) = printTerm t ++ " = 0" 
printConstraint (Le t1 t2) = printTerm t1 ++ " <= " ++ printTerm t2
printConstraint (Ge t1 t2) = printTerm t1 ++ " >= " ++ printTerm t2
printConstraint (Impl c1 c2) = "(" ++ printConstraint c1 ++ ") => (" ++ printConstraint c2 ++ ")"
printConstraint (Not c) = "not (" ++ printConstraint c ++ ")"

instance HasCoeffs Term where
  getCoeffs (CoeffTerm q) = [q]
  getCoeffs (Sum terms) = getCoeffs terms
  getCoeffs (Diff terms) = getCoeffs terms
  getCoeffs (Prod terms) = getCoeffs terms
  getCoeffs _ = []

instance HasCoeffs Constraint where
  getCoeffs (Eq t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Zero t) = getCoeffs t
  getCoeffs (Le t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Ge t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Impl c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (Not c) = getCoeffs c
