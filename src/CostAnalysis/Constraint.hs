{-# LANGUAGE StrictData #-}
{-# LANGUAGE PatternSynonyms #-}

module CostAnalysis.Constraint where

import Prelude hiding (sum)
import Data.List(intercalate)
import qualified Data.Set as S

import CostAnalysis.Coeff
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

termIsZero (ConstTerm 0) = True
termIsZero _ = False

data Constraint
  = Eq Term Term
  | Le Term Term
  | Ge Term Term
  | Impl Constraint Constraint
  | Not Constraint
  deriving (Eq, Ord, Show)

pattern Prod2 :: Term -> Term -> Term 
pattern Prod2 t1 t2 <- Prod [t1, t2]
  where Prod2 t1 t2 = Prod [t1, t2]

eq :: Term -> Term -> [Constraint]
eq (ConstTerm 0) (ConstTerm 0) = []
eq t1 t2 = [Eq t1 t2]

sum :: [Term] -> Term
sum ts | all termIsZero ts = ConstTerm 0
       | otherwise = Sum (filter (not. termIsZero) ts)

prod :: [Term] -> Term
prod ts | any termIsZero ts = ConstTerm 0
       | otherwise = Prod ts

sub :: [Coeff] -> Term
sub qs = Diff (map CoeffTerm qs)

eqSum :: Term -> [Term] -> [Constraint]
eqSum t ts = eq t $ sum ts

eqPlusMulti :: Coeff -> Coeff -> Coeff -> Var -> [Constraint]
eqPlusMulti q p r k = eq (CoeffTerm q) $ Sum [CoeffTerm p, Prod [VarTerm k, CoeffTerm r]]

eqMulti :: Coeff -> Coeff -> Var -> [Constraint]
eqMulti q p k = eq (CoeffTerm q) $ Prod [VarTerm k, CoeffTerm p]

zero :: Term -> [Constraint]
zero t = eq t (ConstTerm 0)

geSum :: [Term] -> Term -> Constraint
geSum ts = Ge (Sum ts)

notZero :: Term -> [Constraint]
notZero t = Not <$> zero t

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
  getCoeffs (Le t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Ge t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Impl c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (Not c) = getCoeffs c
