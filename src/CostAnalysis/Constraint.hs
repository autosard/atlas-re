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

data Term
  = VarTerm Var
  | CoeffTerm Coeff
  | Sum [Term]
  | Diff [Term]
  | Prod [Term]
  | Minus Term
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
  | Or [Constraint]
  | And [Constraint]
  deriving (Eq, Ord, Show)

-- pattern Prod2 :: Term -> Term -> Term 
-- pattern Prod2 t1 t2 <- Prod [t1, t2]
--   where Prod2 t1 t2 = Prod [t1, t2]


eq :: Term -> Term -> [Constraint]
eq (ConstTerm x) (ConstTerm y) | x == y = []
eq t1 t2 = [Eq t1 t2]

sum :: [Term] -> Term
sum ts | all termIsZero ts = ConstTerm 0
       | otherwise = sum' (filter (not. termIsZero) ts)

sum' :: [Term] -> Term
sum' [t] = t
sum' ts = Sum ts

prod :: [Term] -> Term
prod ts | any termIsZero ts = ConstTerm 0
       | otherwise = Prod ts

prod2 :: Term -> Term -> Term
prod2 t1 (ConstTerm 1) = t1
prod2 (ConstTerm 1) t2 = t2
prod2 t1 (ConstTerm (-1)) = minus t1
prod2 (ConstTerm (-1)) t2 = minus t2
prod2 t1 t2 = prod [t1, t2]

sub :: [Term] -> Term
sub [t] = t
sub [t, ConstTerm 0] = t
sub ts | all termIsZero ts = ConstTerm 0
       | otherwise = Diff ts

minus :: Term -> Term
minus = Minus

eqSum :: Term -> [Term] -> [Constraint]
eqSum t ts = eq t $ sum ts

-- eqSumNonZero :: Term -> [Term] -> [Constraint]
-- eqSumNonZero t ts | (not . all termIsZero) ts = eqSum t ts
--                   | otherwise = []


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

geZero :: Term -> [Constraint]
geZero (ConstTerm 0) = []
geZero t = ge t (ConstTerm 0)

le :: Term -> Term -> [Constraint]
le t1 t2 | t1 == t2 = []
le t1 t2 = [Le t1 t2]

ge :: Term -> Term -> [Constraint]
ge t1 t2 | t1 == t2 = []
ge t1 t2 = [Ge t1 t2]


-- empty list corresponds to a true constraint
impl :: [Constraint] -> [Constraint] -> [Constraint]
impl [] [] = []
impl [] [c2] = [c2]
impl [c1] [] = []
impl [c1] [c2] = [Impl c1 c2]
impl _ _ = error "cannot construct implication. "

or :: [Constraint] -> [Constraint]
or [] = []
or cs = [Or cs]

or2 :: [Constraint] -> [Constraint] -> [Constraint]
or2 [] _ = []
or2 _ [] = []
or2 xs ys = or (xs ++ ys)

and :: [Constraint] -> [Constraint]
and cs = [And cs]

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
printConstraint (Or cs) = "or (" ++ intercalate "," (map printConstraint cs) ++ ")"

instance HasCoeffs Term where
  getCoeffs (CoeffTerm q) = [q]
  getCoeffs (Sum terms) = getCoeffs terms
  getCoeffs (Diff terms) = getCoeffs terms
  getCoeffs (Prod terms) = getCoeffs terms
  getCoeffs (Minus term) = getCoeffs term
  getCoeffs _ = []

instance HasCoeffs Constraint where
  getCoeffs (Eq t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Le t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Ge t1 t2) = getCoeffs t1 ++ getCoeffs t2
  getCoeffs (Impl c1 c2) = getCoeffs c1 ++ getCoeffs c2
  getCoeffs (Not c) = getCoeffs c
  getCoeffs (Or cs) = getCoeffs cs
  getCoeffs (And cs) = getCoeffs cs
