{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}


module Syntax.FreeModule
  ( FreeModule
  , singleton
  , singleton'
  , fromList
  , fromList'
  , empty
  , add
  , scale
  , sum
  , coeffSum
  , linSubst
  , unit
  , mult
  , prod
  , basis
  , map
  , linMap
  , bimap
  , partitions
  , mapMaybe
  ) where

import Prelude hiding (sum, map)
import qualified Prelude (sum, map)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Primitive as P (partitions)
import qualified Data.Maybe (mapMaybe)

import Syntax.PrettyPrint (PrettyPrint (..))
import Data.List (intercalate)
import Syntax (HasVars (..))
import qualified Data.Set as S

-- invariant: never contains entries with zero coeffients
type FreeModule a b = Map a b

clean :: (Eq b, Num b) => FreeModule a b -> FreeModule a b
clean = M.filter (/= 0)

singleton :: (Num b) =>  a -> FreeModule a b
singleton = (`M.singleton` 1)

singleton' :: (Num b) =>  a -> b -> FreeModule a b
singleton' = M.singleton

fromList :: (Ord a, Num b, Eq b) => [a] -> FreeModule a b
fromList = sum . Prelude.map singleton

fromList' :: (Ord a, Num b, Eq b) => [(a, b)] -> FreeModule a b
fromList' = clean . M.fromList 

empty :: FreeModule a b
empty = M.empty

add :: (Ord a, Num b, Eq b) => FreeModule a b -> FreeModule a b -> FreeModule a b
add m1 m2 = clean $ M.unionWith (+) m1 m2

sum :: (Ord a, Num b, Eq b) => [FreeModule a b] -> FreeModule a b
sum = foldr add empty

scale :: (Num b, Eq b) => b -> FreeModule a b -> FreeModule a b
scale k = clean . M.map (* k)

coeffSum :: (Num b) => FreeModule a b -> b
coeffSum = Prelude.sum . M.elems


linSubst :: (Ord a, Num b, Eq b) => a -> FreeModule a b -> FreeModule a b -> FreeModule a b
linSubst x n m
  | M.member x m =
      let k = m M.! x
          m' = M.delete x m in
        add (scale k n) m'
  | otherwise = m                     

unit :: (Monoid a, Num b) => FreeModule a b
unit = singleton mempty

mult :: (Monoid a, Num b, Ord a) => FreeModule a b -> FreeModule a b -> FreeModule a b
mult m n = M.fromList [ (a <> b, k * l)
                      | (a, k) <- M.toList m,
                        (b, l) <- M.toList n]

prod :: (Monoid a, Num b, Ord a) => [FreeModule a b] -> FreeModule a b
prod = foldr mult unit 

basis :: FreeModule a b -> Set a
basis = M.keysSet

map :: (Ord c) => (a -> c) -> FreeModule a b -> FreeModule c b
map = M.mapKeys

mapMaybe :: (Ord c) => (a -> Maybe c) -> FreeModule a b -> FreeModule c b
mapMaybe f = M.fromList . Data.Maybe.mapMaybe (\(k, v) -> (,v) <$> f k) . M.toList

linMap :: (Ord a, Ord c, Num b, Ord b) => (a -> FreeModule c b) -> FreeModule a b -> FreeModule c b
linMap f m = sum . Prelude.map go $ M.toList (map f m)
  where go (n, k) = scale k n

bimap :: (Ord a', Ord b') => (a -> a') -> (b -> b') -> FreeModule a b -> FreeModule a' b'
bimap f g = M.mapKeys f . M.map g

instance (PrettyPrint a, Show b) => PrettyPrint (FreeModule a b) where
  prettyPrint m = intercalate " + " $ Prelude.map ppProd (M.toList m)
    where ppProd (a, k) = show k ++ " * " ++ prettyPrint a 

-- generate all k-partitions for given module
partitions :: (Ord a, Num b, Eq b) => Int -> FreeModule a b -> [[FreeModule a b]]
partitions k m = do
  parts <- Prelude.filter (\p -> length p <= k)
    $ P.partitions $ M.toList m
  return (Prelude.map fromList' parts)
  
instance (HasVars a) => HasVars (FreeModule a b) where
  freeVars = S.unions . S.map freeVars . M.keysSet 
  
