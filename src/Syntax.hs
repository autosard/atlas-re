{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Syntax
  ( Fqn
  , Id
  , enumId
  , Parsed
  , Elaborated
  , Typed
  , Positioned
  , HasVars (..)
  , Substitutable (..)
  , substVar
  , substVars
  , HasProduct (..)
  , normalisedProd
  ) where

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet

--------------------------------------------------------------------------------
-- Stages
--------------------------------------------------------------------------------
-- We use extensible AST types to model the different stages (parsed, typed, etc.) (see https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf)

data Parsed
data Elaborated
data Typed
data Positioned

type Fqn = (Text, Text)

type Id = Text

enumId :: Int -> Id
enumId n = T.pack $ "?" ++ show n

--------------------------------------------------------------------------------
-- Free Variables & Substitution
--------------------------------------------------------------------------------

class Substitutable a where
  subst :: M.Map Id Id -> a -> a

instance (Substitutable a) => Substitutable [a] where
  subst s = map (subst s)

instance (Ord a, Substitutable a) => Substitutable (Set a) where
  subst s = S.map (subst s)

instance Substitutable Id where
  subst env var = M.findWithDefault var var env

class HasVars a where
  freeVars :: a -> Set Id

instance (HasVars a) => HasVars [a] where
  freeVars l = S.unions (map freeVars l)

instance (HasVars a) => HasVars (Set a) where
  freeVars l = S.unions (S.map freeVars l)  

substVar :: (Substitutable a) => Id -> Id -> a -> a
substVar x y = subst (M.singleton x y)

substVars :: (Substitutable a) => [Id] -> [Id] -> a -> a
substVars xs ys = subst (M.fromList (zip xs ys)) 

class (Eq a) => HasProduct a where
  one :: a
  prod :: MultiSet a -> a
  unprod :: a -> Maybe (MultiSet a)


normProd :: (HasProduct a) => a -> a
normProd t = case unprod t of
  Just ts 
    | all (== one) ts -> one
    | otherwise       -> prod ts
  Nothing -> t

normalisedProd :: (HasProduct a, Ord a) => a -> a -> a
normalisedProd t s = combine (normProd s) (normProd t)
  where combine t s
          | t == one = t
          | s == one = s
          | otherwise = case (unprod t, unprod s) of
              (Just ts, Just ss) -> prod $ MSet.union ts ss
              (Nothing, Just ss) -> prod $ MSet.insert t ss
              (Just ts, Nothing) -> prod $ MSet.insert s ts
              (Nothing, Nothing) -> prod $ MSet.fromList [t, s]  
