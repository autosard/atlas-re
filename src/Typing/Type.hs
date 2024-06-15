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

splitFnType :: Type -> (Type, Type)
splitFnType (TAp Arrow [from, to]) = (from, to)
splitFnType t = error $ "Cannot split function type: got invalid function type '" ++ show t ++ "'."

treeValueType :: Type -> Type
treeValueType (TAp Tree [t]) = t
treeValueType t = error "Got non-tree type."

splitTupleType :: Type -> (Type, Type)
splitTupleType (TAp Prod [x1, x2]) = (x1, x2)
splitTupleType t = error "Got non-tuple type."

countTrees :: Type -> Int
countTrees (TAp Tree _) = 1
countTrees (TAp Prod ts) = sum . map countTrees $ ts
countTrees _ = 0

isTree :: Type -> Bool
isTree (TAp Tree _) = True
isTree _ = False

isBool :: Type -> Bool
isBool (TAp Bool []) = True
isBool _ = False
