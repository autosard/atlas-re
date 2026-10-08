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
  , fromRScalar
  , isNonlinear
  , hasVars
  , substFormula
  )where

import Prelude hiding (sum, or)

import CostAnalysis.Coeff
import Data.Map (Map)
import qualified Data.Map as M
import Syntax.ResourceExpression (RScalar (..))

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

fromRScalar :: RScalar -> ArithExpr
fromRScalar (RSConst k) = ConstTerm k
fromRScalar (RSCoeff i t) = CoeffTerm (Coeff i t)
fromRScalar (RSAdd s1 s2) = sum [fromRScalar s1, fromRScalar s2]
fromRScalar (RSMul s1 s2) = prod2 (fromRScalar s1) (fromRScalar s2) 

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

-- | Contains a product of two non-constant factors.
isNonlinear :: Formula -> Bool
isNonlinear = anyArith go
  where go (Prod ts) = length (filter (not . isConst) ts) > 1 || any go ts
        go (Sum ts) = any go ts
        go (Diff ts) = any go ts
        go (Minus t) = go t
        go _ = False
        isConst (ConstTerm _) = True
        isConst _ = False

-- | Contains a variable or a Boolean atom besides coefficients.
hasVars :: Formula -> Bool
hasVars (Atom _) = True
hasVars (Impl a b) = hasVars a || hasVars b
hasVars (Iff a b) = hasVars a || hasVars b
hasVars (Not a) = hasVars a
hasVars (Or fs) = any hasVars fs
hasVars (And fs) = any hasVars fs
hasVars f = anyArith go f
  where go (VarTerm _) = True
        go (Sum ts) = any go ts
        go (Diff ts) = any go ts
        go (Prod ts) = any go ts
        go (Minus t) = go t
        go _ = False

anyArith :: (ArithExpr -> Bool) -> Formula -> Bool
anyArith p (Eq a b) = p a || p b
anyArith p (Le a b) = p a || p b
anyArith p (Ge a b) = p a || p b
anyArith p (Impl a b) = anyArith p a || anyArith p b
anyArith p (Iff a b) = anyArith p a || anyArith p b
anyArith p (Not a) = anyArith p a
anyArith p (Or fs) = any (anyArith p) fs
anyArith p (And fs) = any (anyArith p) fs
anyArith _ _ = False

-- | Replaces coefficients by their values.
substFormula :: Map Coeff Rational -> Formula -> Formula
substFormula vals f | M.null vals = f
substFormula vals f = case f of
  Eq a b -> Eq (go a) (go b)
  Le a b -> Le (go a) (go b)
  Ge a b -> Ge (go a) (go b)
  Impl a b -> Impl (substFormula vals a) (substFormula vals b)
  Iff a b -> Iff (substFormula vals a) (substFormula vals b)
  Not a -> Not (substFormula vals a)
  Or fs -> Or (map (substFormula vals) fs)
  And fs -> And (map (substFormula vals) fs)
  _ -> f
  where go (CoeffTerm q) = maybe (CoeffTerm q) ConstTerm (M.lookup q vals)
        go (Sum ts) = Sum (map go ts)
        go (Diff ts) = Diff (map go ts)
        go (Prod ts) = Prod (map go ts)
        go (Minus t) = Minus (go t)
        go t = t
