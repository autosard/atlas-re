{-# LANGUAGE StrictData #-}
{-# LANGUAGE PatternSynonyms #-}

module Typing.Type where

import qualified Data.Text as T
import Data.List(intercalate)

import Primitive(Id)

newtype Tyvar = Tyvar Id 
  deriving (Eq, Ord, Show)

data Tycon = Num
  | Base
  | Bool
  | Tree
  | List
  | Prod
  | Arrow
  deriving (Eq, Ord, Show)

data Type
  = TVar Tyvar
  | TAp Tycon [Type]
  | TGen Int
  deriving (Eq, Ord)

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

splitProdType :: Type -> [Type]
splitProdType (TAp Prod ts) = ts
splitProdType t = [t]

countTrees :: Type -> Int
countTrees (TAp Tree _) = 1
countTrees (TAp Prod ts) = sum . map countTrees $ ts
countTrees _ = 0

isProd :: Type -> Bool
isProd (TAp Prod _) = True
isProd _ = False

isSimpleProd :: Type -> Bool
isSimpleProd (TAp Prod ts) = (not . any isProd) ts
isSimpleProd _ = False


isTree :: Type -> Bool
isTree (TAp Tree _) = True
isTree _ = False

isBool :: Type -> Bool
isBool (TAp Bool []) = True
isBool _ = False

isBase (TAp Bool []) = True
isBase (TAp Num []) = True
isBase _ = False

notNested :: Type -> Bool
notNested (TAp List [t]) | isBase t = True
notNested (TAp Tree [t]) | isBase t = True
notNested _ = True

-- no proper unification just top level check
matchesType :: Type -> Type -> Bool
matchesType (TAp c1 _) (TAp c2 _) | c1 == c2 = True
matchesType _ _ = False

matchesTypes :: Type -> [Type] -> Bool
matchesTypes t = any (matchesType t)

pattern TreeType :: Type
pattern TreeType <- TAp Tree [TAp Base []]
  where TreeType = TAp Tree [TAp Base []]

pattern ListType :: Type
pattern ListType <- TAp List [TAp Base []]
  where ListType = TAp List [TAp Base []]
