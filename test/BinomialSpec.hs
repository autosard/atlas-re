{-# LANGUAGE OverloadedStrings #-}

-- | The binomial normalisation must preserve the value of binom(u, k) as a
-- polynomial: the normalised expression is evaluated at all small sizes and
-- compared with the direct value of the generalised binomial coefficient.
module BinomialSpec (spec) where

import Test.Hspec
import qualified Data.Map as M
import qualified Data.MultiSet as MSet

import Syntax.ResourceExpression
import Syntax.ResourceExpression.Binomial (normBinom)

binomQ :: Rational -> Int -> Rational
binomQ u k = product [ (u - fromIntegral i) / fromIntegral (i + 1) | i <- [0 .. k - 1] ]

evalSize :: M.Map SizeTerm Rational -> SizeExpr -> Rational
evalSize env ss = sum [ c * M.findWithDefault 1 t env | (t, c) <- M.toList ss ]

evalTerm :: M.Map SizeTerm Rational -> ResourceTerm -> Rational
evalTerm _ RTId = 1
evalTerm env (RTBinom ss k) = binomQ (evalSize env ss) k
evalTerm env (RTProd ts) = product (map (evalTerm env) (MSet.toList ts))
evalTerm _ t = error $ "unexpected term " ++ show t

evalExpr :: M.Map SizeTerm Rational -> ResourceExpr -> Rational
evalExpr env e = sum [ scalar c * evalTerm env t | (t, c) <- M.toList e ]
  where scalar (RSConst r) = r
        scalar s = error $ "unexpected scalar " ++ show s

-- | binom(cx |x| + cy |y| + c, k)
sizeExpr :: Rational -> Rational -> Rational -> SizeExpr
sizeExpr cx cy c = M.fromList $
  [(SVar "x", cx) | cx /= 0] ++ [(SVar "y", cy) | cy /= 0] ++ [(SId, c) | c /= 0]

preserves :: Rational -> Rational -> Rational -> Int -> Bool
preserves cx cy c k = and
  [ evalExpr env (normBinom ss k) == binomQ (evalSize env ss) k
  | a <- [0 .. 6], b <- [0 .. 6]
  , let env = M.fromList [(SVar "x", a), (SVar "y", b), (SId, 1)] ]
  where ss = sizeExpr cx cy c

spec :: Spec
spec = describe "binomial normalisation" $ do
  it "preserves the value for integer coefficients and constants" $
    [ (cx, cy, c, k) | cx <- [-2 .. 3], cy <- [-2 .. 2], c <- [-2 .. 2], k <- [1 .. 3]
                     , (cx, cy) /= (0, 0), not (preserves cx cy c k) ] `shouldBe` []
  it "preserves the value for fractional coefficients with k = 1" $
    [ (cx, c) | cx <- [1/3, 1/2, -3/2], c <- [-1/2, 0, 2]
              , not (preserves cx 1 c 1) ] `shouldBe` []
