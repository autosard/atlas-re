-- | Expansion of resource terms into polynomials over sizes, for displaying
-- bounds as polynomials instead of binomial coefficients, e.g.
-- binom(|x|, 1) + binom(|x|, 2) as ½·|x|² + ½·|x|. Terms that are not
-- polynomial in the sizes (logarithms, potentials) are kept as opaque atoms,
-- so |x|·log(|x|) is a monomial of two atoms.
module Syntax.ResourceExpression.Polynomial
  ( Polynomial
  , Atom (..)
  , Monomial
  , fromTerm
  , fromBound
  , monomials
  ) where

import Data.Map (Map)
import qualified Data.Map as M
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet

import Syntax (Id)
import Syntax.ResourceExpression

data Atom = AVar Id | AOpaque ResourceTerm
  deriving (Eq, Ord, Show)

type Monomial = MultiSet Atom

-- | Polynomial with rational coefficients; zero coefficients are not stored.
newtype Polynomial = Polynomial (Map Monomial Rational)
  deriving (Eq, Show)

monomials :: Polynomial -> [(Monomial, Rational)]
monomials (Polynomial m) = M.toList m

mkPoly :: Map Monomial Rational -> Polynomial
mkPoly = Polynomial . M.filter (/= 0)

atom :: Atom -> Polynomial
atom a = Polynomial (M.singleton (MSet.singleton a) 1)

instance Num Polynomial where
  Polynomial p + Polynomial q = mkPoly (M.unionWith (+) p q)
  Polynomial p * Polynomial q = mkPoly $ M.fromListWith (+)
    [ (MSet.union m n, a * b) | (m, a) <- M.toList p, (n, b) <- M.toList q ]
  negate (Polynomial p) = Polynomial (M.map negate p)
  fromInteger c = mkPoly (M.singleton MSet.empty (fromInteger c))
  abs = error "Polynomial: abs"
  signum = error "Polynomial: signum"

scale :: Rational -> Polynomial -> Polynomial
scale k (Polynomial p) = mkPoly (M.map (k *) p)

polySize :: SizeExpr -> Polynomial
polySize s = sum [ scale k (fromSizeTerm t) | (t, k) <- M.toList s ]
  where fromSizeTerm (SVar x) = atom (AVar x)
        fromSizeTerm SId = 1

-- | binom(u, k) = u (u - 1) ... (u - k + 1) / k!
fromTerm :: ResourceTerm -> Polynomial
fromTerm (RTSize x) = atom (AVar x)
fromTerm (RTBinom s k) = scale (1 / fromInteger (product [1 .. fromIntegral k]))
  (product [ polySize s - fromIntegral i | i <- [0 .. k - 1] ])
fromTerm (RTProd ts) = product (map fromTerm (MSet.toList ts))
fromTerm RTId = 1
fromTerm t = atom (AOpaque t)

fromBound :: Map ResourceTerm Rational -> Polynomial
fromBound m = sum [ scale k (fromTerm t) | (t, k) <- M.toList m ]
