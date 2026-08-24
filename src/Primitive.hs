{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module Primitive
  ( dbg
  , toIntegerExact
  , unionMap
  ) where

import Data.Set(Set)
import qualified Data.Set as S
import Data.Ratio
import Debug.Trace hiding (traceShow)

dbg :: String -> (a -> String) -> a -> a
dbg label f x = trace (label ++ ": " ++ f x) x

data IntWithInf = Inf | NotInf Int
  deriving Eq

instance Num IntWithInf where
  (+) Inf _ = Inf
  (+) _ Inf = Inf
  (+) (NotInf x) (NotInf y) = NotInf (x + y)
  (-) Inf _ = Inf
  (-) _ Inf = error "can not subtract integer from infinity"
  (-) (NotInf x) (NotInf y) = NotInf (x - y)
  (*) Inf _ = Inf
  (*) _ Inf = Inf
  (*) (NotInf x) (NotInf y) = NotInf (x * y)
  abs Inf = Inf
  abs (NotInf x) = NotInf (abs x)
  signum Inf = 1
  signum (NotInf x) = NotInf (signum x)
  fromInteger x = NotInf $ fromInteger x
  
instance Ord IntWithInf where
  (<=) Inf _ = False
  (<=) _ Inf = True
  (<=) (NotInf x) (NotInf y) = x <= y

toIntegerExact :: Rational -> Maybe Integer
toIntegerExact r
  | denominator r == 1 = Just (numerator r)
  | otherwise          = Nothing             


unionMap :: (Ord b) => (a -> Set b) -> [a] -> Set b
unionMap f xs = S.unions $ map f xs


