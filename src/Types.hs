{-# LANGUAGE OverloadedStrings #-}

module Types where

import Data.Map(Map)
import qualified Data.Map.Strict as M
import Data.List(union)
import qualified Data.Text as T

import Primitive(Id)

import Debug.Trace(trace)
traceShow s v = trace (s ++ ": " ++ show v) v

data Tyvar = Tyvar Id 
  deriving (Eq, Ord, Show)

enumId :: Int -> Id
enumId n = T.pack $ "?:" ++ (show n)

-- Type constructor of arity n
data Tycon = Num
  | Bool
  | Tree
  | Prod
  | Arrow
  deriving (Eq, Show)

data Type
  = TVar Tyvar
  | TAp Tycon [Type]
  | TGen Int
  deriving (Eq, Show)

data Scheme = Forall Int Type
  deriving (Eq, Show)

treeT = Forall 1 (TAp Tree [TGen 0])
tupleT = Forall 2 (TAp Prod [TGen 0, TGen 1])
boolT = Forall 0 (TAp Bool [])

nAryFn :: Int -> Scheme
nAryFn n = Forall (n+1) $ TAp Arrow [TAp Prod $ map TGen [0..(n-1)], TGen n] ;


type Subst = Map Tyvar Type

nullSubst = M.empty

(+->) :: Tyvar -> Type -> Subst
u +-> t = M.singleton u t

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [Tyvar]

instance Types Type where
  apply s (TVar u)  = case M.lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp c ts) = TAp c (apply s ts)
  tv (TVar u)  = [u]
  tv (TAp c ts) = tv ts

instance Types a => Types [a] where
  apply s = map (apply s)
  tv = foldr (union . tv) []

instance Types Scheme where
  apply s (Forall n t) = Forall n (apply s t)
  tv (Forall _ t) = tv t

infix 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = (M.map (apply s1) s2) `M.union` s1

