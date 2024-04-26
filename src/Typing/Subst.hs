module Typing.Subst where

import Data.Map(Map)
import qualified Data.Map.Strict as M
import Data.List(union)

import Typing.Type

type Subst = Map Tyvar Type

nullSubst = M.empty

infix 4 +->
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
  apply s t = t
  tv (TVar u)  = [u]
  tv (TAp c ts) = tv ts
  tv t = []

instance Types a => Types [a] where
  apply s = map (apply s)
  tv = foldr (union . tv) []

infix 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = M.map (apply s1) s2 `M.union` s1
