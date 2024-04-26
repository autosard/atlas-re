{-# LANGUAGE StrictData #-}

module Typing.Type where

import Primitive(Id)

newtype Tyvar = Tyvar Id 
  deriving (Eq, Ord, Show)

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

fn :: [Type] -> Type -> Type
fn from to = TAp Arrow [TAp Prod from, to]

