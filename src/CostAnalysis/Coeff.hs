{-# LANGUAGE StrictData #-}

module CostAnalysis.Coeff where

import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.List as L

import Primitive(Id)

data Coeff
  = Unknown Int Text Text CoeffIdx
  | Known Int Text Text CoeffIdx Rational
  deriving (Eq, Ord, Show)

printCoeff :: Coeff -> String
printCoeff (Known _ _ _ _ v) = show v

data Factor = Const Int | Arg Id Int
  deriving (Eq, Ord)

instance Show Factor where
  show (Const c) = show c
  show (Arg x a) = T.unpack x ++ "^" ++ show a

infixl 9 ^
(^) :: Id -> Int -> Factor
(^) = Arg

data CoeffIdx = Pure Id | Mixed (Set Factor)
  deriving (Eq, Ord)

instance Show CoeffIdx where
  show (Pure x) = "(" ++ T.unpack x ++ ")"
  show (Mixed xs) = "(" ++ L.intercalate "," (map show (S.toDescList xs)) ++ ")"

type CoeffsMap = Map CoeffIdx Coeff
