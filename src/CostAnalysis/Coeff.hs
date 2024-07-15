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
  = AnnCoeff -- ^ Annotation coefficient 
    Int -- ^ Unique identifier for the annotation; used together with coefficent index to identify coeffients when encoding them for smt. 
    Text -- ^ Human readable label, e.g. \"Q\", \"P\", ...
    Text -- ^ Human readable comment, to trace the origin of the coefficient, e.g. "log".
    CoeffIdx -- ^ An index to identify the coefficient.
  | GenCoeff -- ^ Generic coefficient
    Int -- ^ Unique identifier
  deriving (Eq, Ord, Show)

printCoeff :: Coeff -> String
printCoeff (AnnCoeff id label comment idx) = "q" ++ show id ++ "_" ++ show idx
  ++ "{" ++ T.unpack label ++ "," ++ T.unpack comment ++ "}"

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

substitute :: CoeffIdx -> Id -> CoeffIdx
substitute (Pure x) y = Pure y
substitute (Mixed factors) y = Mixed (S.map (subFactor y) factors)
  where subFactor _ (Const c) = Const c 
        subFactor y (Arg x a) = Arg y a



type CoeffsMap = Map CoeffIdx Coeff
