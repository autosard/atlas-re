-- | Normalisation of binomial coefficients over size expressions.
--
-- A term binom(u, k) whose argument u is not a single size |x| arises when a
-- size measure is unfolded or a size transformer is substituted. 'normBinom'
-- rewrites it into a linear combination of products of binom(|x|, j), and
-- 'mergeBinoms' merges binomial factors of the same size in a product. The
-- rewriting uses the following identities, all of which are identities of
-- polynomials, with binom(u, k) = u (u - 1) ... (u - k + 1) / k! for any u:
--
-- * Pascal:          binom(x + 1, k) = binom(x, k) + binom(x, k - 1)
-- * Vandermonde:     binom(u + v, k) = sum_j binom(u, j) binom(v, k - j),
--                    also with a constant summand v = c (c an integer)
-- * coefficients:    c x = x + ... + x, and binom(-x, a) = (-1)^a binom(x + a - 1, a)
-- * products:        binom(x, a) binom(x, b)
--                      = sum_i (a + b - i)! / (i! (a - i)! (b - i)!) binom(x, a + b - i)
-- * linear case:     binom(u, 1) = u for any linear u
--
-- Soundness. The rewritten expression equals binom(u, k) at every point, so
-- for an exact size transformer (u is the size of a value, a natural number)
-- the meaning is preserved. For an inexact transformer (|r| <= u) the analysis
-- additionally relies on monotonicity, binom(|r|, k) <= binom(u, k), which holds
-- since u is a natural number when the coefficients are integers (u >= |r| >= 0).
-- Fractional coefficients are therefore only supported for k = 1 (where
-- binom(u, 1) = u is monotone for all u); otherwise normalisation fails.
module Syntax.ResourceExpression.Binomial
  ( normBinom
  , mergeBinoms
  ) where

import qualified Data.Map as M
import qualified Data.MultiSet as MSet
import Data.Ratio (denominator, numerator)

import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM

-- | Merges binomial factors of the same variable in a product:
-- binom(x, a) * binom(x, b) is the sum over i = 0 .. min(a, b) of
-- (a + b - i)! / (i! (a - i)! (b - i)!) * binom(x, a + b - i),
-- e.g. binom(x, 1) * binom(x, 1) = 2 binom(x, 2) + binom(x, 1).
mergeBinoms :: ResourceTerm -> ResourceExpr
mergeBinoms t@(RTProd ts) = case pick (MSet.toList ts) of
  Nothing -> FM.singleton t
  Just (x, a, b, rest) -> FM.sum
    [ FM.scale (RSConst (fromInteger m)) (mergeBinoms (foldr (<>) (RTBinom (FM.singleton (SVar x)) (a + b - i)) rest))
    | i <- [0 .. min a b]
    , let m = fac (a + b - i) `div` (fac i * fac (a - i) * fac (b - i)) ]
  where
    single (RTBinom ss k) | [(SVar x, 1)] <- M.toList ss = Just (x, k)
    single _ = Nothing
    -- two factors binom(x, a) and binom(x, b) of the same variable x
    pick fs = case [ (x, a, b, deleteAt k others)
                   | (i, f) <- zip [0 :: Int ..] fs, Just (x, a) <- [single f]
                   , let others = deleteAt i fs
                   , (k, g) <- zip [0 :: Int ..] others, Just (y, b) <- [single g], y == x ] of
      (found : _) -> Just found
      [] -> Nothing
    deleteAt i xs = take i xs ++ drop (i + 1) xs
    fac :: Int -> Integer
    fac n = product [1 .. fromIntegral n]
mergeBinoms t = FM.singleton t

normBinom :: SizeExpr -> Int -> ResourceExpr
normBinom _ 0 = FM.singleton RTId
normBinom ss k = case (vars, M.findWithDefault 0 SId ss) of
  -- constant argument: binom(c, k) for a natural number c
  ([], c) -> let b = binomial c k in
    if b == 0 then FM.empty else FM.singleton' RTId (RSConst b)
  -- binom(x, k)
  ([x], 0) | coeff x == 1 -> FM.singleton $ RTBinom (FM.singleton x) k
  -- Pascal: binom(x + 1, k) = binom(x, k) + binom(x, k - 1)
  ([x], 1) | coeff x == 1 -> FM.fromList $ RTBinom (FM.singleton x) k :
    [ if k == 1 then RTId else RTBinom (FM.singleton x) (k - 1) ]
  -- Vandermonde: binom(x_1 + ... + x_n, k) is the sum of the products
  -- binom(x_1, a_1) * ... * binom(x_n, a_n) with a_1 + ... + a_n = k
  (xs, 0) | all ((== 1) . coeff) xs -> FM.fromList
    [ prodOf [RTBinom (FM.singleton x) a | (x, a) <- zip xs as, a > 0]
    | as <- compositions (length xs) k ]
  -- Vandermonde with a constant: binom(x_1 + ... + x_n + c, k) is the sum of
  -- binom(c, k - j) * binom(x_1 + ... + x_n, j) for a natural number c
  (xs, c) | all ((== 1) . coeff) xs && c > 0 && denominator c == 1 -> FM.sum
    [ FM.scale (RSConst b) (normBinom (M.delete SId ss) j)
    | j <- [0 .. k], let b = binomial c (k - j), b /= 0 ]
  -- integer coefficients: c x is x + ... + x (c times), so Vandermonde applies
  -- to the variables with repetitions; factors of the same variable are then
  -- merged, e.g. binom(2x, 2) = 2 binom(x, 2) + binom(x, 1) binom(x, 1)
  --                           = 4 binom(x, 2) + binom(x, 1).
  -- A negative coefficient contributes copies of -x, with
  -- binom(-x, a) = (-1)^a binom(x + a - 1, a). The constant c may be negative
  -- as well (e.g. |e| - 1 from a size transformer), binom(-1, m) = (-1)^m.
  -- All of these are polynomial identities.
  (xs, c) | all (integral . coeff) xs && integral c ->
    let copies = concat [ replicate (fromInteger (abs n)) (x, n > 0)
                        | x <- xs, let n = numerator (coeff x) ]
        factor _ 0 = FM.singleton RTId
        factor (x, True) a = FM.singleton (RTBinom (FM.singleton x) a)
        factor (x, False) a = FM.fromList'
          [ (if i == 0 then RTId else RTBinom (FM.singleton x) i, RSConst ((-1) ^ a * b))
          | i <- [0 .. a], let b = binomial (fromIntegral a - 1) (a - i), b /= 0 ]
        expand j = FM.linMap mergeBinoms $ FM.sum
          [ FM.prod [ factor cp a' | (cp, a') <- zip copies as ]
          | as <- compositions (length copies) j ] in
    FM.sum [ FM.scale (RSConst b) (expand j)
           | j <- [0 .. k], let b = binomial c (k - j), b /= 0 ]
  -- binom(c_1 x_1 + ... + c_n x_n + c, 1) = c_1 binom(x_1, 1) + ... + c_n binom(x_n, 1) + c
  -- for arbitrary coefficients (binom(u, 1) = u), e.g. for the size
  -- |l| - |i| of an exact size transformer
  (xs, c) | k == 1 -> FM.fromList' $
    [(RTBinom (FM.singleton x) 1, RSConst (coeff x)) | x <- xs]
    ++ [(RTId, RSConst c) | c /= 0]
  (xs, c) -> error $ "cannot normalise arbitrary sums in binomial coeffients: " ++ show xs ++ show c ++ show k
  where
    vars = filter (/= SId) (M.keys ss)
    integral r = denominator r == 1
    coeff x = ss M.! x
    prodOf [] = RTId
    prodOf [b] = b
    prodOf bs = RTProd (MSet.fromList bs)
    -- all ways to write k as an ordered sum of n natural numbers
    compositions :: Int -> Int -> [[Int]]
    compositions 0 0 = [[]]
    compositions 0 _ = []
    compositions n m = [a : rest | a <- [0 .. m], rest <- compositions (n - 1) (m - a)]
    binomial :: Rational -> Int -> Rational
    binomial c m = product [ (c - fromIntegral i) / fromIntegral (i + 1) | i <- [0 .. m - 1] ]
