{-# LANGUAGE StrictData #-}

module Typing.Type where

import qualified Data.Text as T
import Data.List(intercalate)

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
  deriving (Eq)

instance Show Type where
  show (TVar (Tyvar var)) = T.unpack var
  show (TAp Arrow [l, r]) = show l ++ " " ++ "->" ++ " " ++ show r
  show (TAp Prod ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
  show (TAp const ts) = show const ++ " " ++ unwords (map show ts) 
  show (TGen i) = "a" ++ show i

fn :: [Type] -> Type -> Type
fn [] to = to
fn from to = TAp Arrow [TAp Prod from, to]

