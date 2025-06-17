{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Predicate where

import qualified Data.Set as S
import Data.Set(Set)

import Primitive(Id)
import Ast 
import Control.Monad (guard)

data PredOp = Le | Lt | Eq | Neq
  deriving (Eq, Ord)

data Predicate = Predicate Id PredOp Id Id
  deriving (Eq, Ord)

predVars :: Predicate -> Set Id
predVars (Predicate _ _ x y) = S.fromList [x,y]

hasVars :: Set Id -> Predicate ->  Bool
hasVars vars p = not . S.null $ predVars p `S.intersection` vars

excludeByVars :: Set Predicate -> Set Id -> Set Predicate
excludeByVars ps vars = S.filter (not . hasVars vars) ps

restrictByVars :: Set Predicate -> Set Id -> Set Predicate
restrictByVars ps vars = S.filter (hasVars vars) ps

measure ::  PositionedExpr -> Maybe (Id, Id)
measure (Const m [Var x]) = Just (m,x)
measure _ = Nothing

predFromCondition :: PositionedExpr -> Maybe Predicate
predFromCondition (Const "EQ" args) = buildPredicate Eq args
predFromCondition (Const "LE" args) = buildPredicate Le args
predFromCondition (Const "LT" args) = buildPredicate Lt args
predFromCondition (Const "GE" [x,y]) = buildPredicate Le [y,x]
predFromCondition (Const "GT" [x,y]) = buildPredicate Lt [y,x]
predFromCondition _ = Nothing

buildPredicate :: PredOp -> [PositionedExpr] -> Maybe Predicate
buildPredicate op [arg1, arg2] = do
  (m1, x) <- measure arg1
  (m2, y) <- measure arg2
  guard (m1 == m2)
  return (Predicate m1 op x y)

negate :: Predicate -> Predicate
negate (Predicate m Eq x y) = Predicate m Neq x y
negate (Predicate m Neq x y) = Predicate m Eq x y
negate (Predicate m Le x y) = Predicate m Lt y x
negate (Predicate m Lt x y) = Predicate m Le y x

