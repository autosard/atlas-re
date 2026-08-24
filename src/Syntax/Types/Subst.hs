module Syntax.Types.Subst
  ( Types (..)
  , Subst
  , nullSubst
  , (+->)
  , (@@)
  )where

import Data.Map(Map)
import qualified Data.Map.Strict as M
import Data.List(union)

import Syntax (Id)
import Syntax.Types.Type

type Subst = Map Id Type

nullSubst = M.empty

infix 4 +->
(+->) :: Id -> Type -> Subst
u +-> t = M.singleton u t

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [Id]

instance Types Type where
  apply s (TVar u)  = case M.lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp c ts) = TAp c (apply s ts)
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply s t = t
  tv (TVar u)  = [u]
  tv (TAp c ts) = tv ts
  tv (TFun t1 t2) = tv t1 `union` tv t2
  tv t = []

instance Types a => Types [a] where
  apply s = map (apply s)
  tv = foldr (union . tv) []


infix 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = M.map (apply s1) s2 `M.union` s1
