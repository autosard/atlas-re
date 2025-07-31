{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Predicate where

import Prelude hiding (or)

import Data.Set(Set)
import qualified Data.Map as M
import Data.Map(Map)

import Primitive(Id, Substitution, applySubst)
import Control.Monad (guard)
import qualified Data.Set as S
import CostAnalysis.Constraint (or, Constraint)
import Ast hiding (PotentialKind(..))
import qualified Ast as A (PotentialKind(..))
import Typing.Type

import CostAnalysis.Annotation(Measure(..))

data PredOp = Le | Lt | Eq | Neq
  deriving (Eq, Ord, Show)

measureFromConst :: Id -> Maybe Measure
measureFromConst "weight" = Just Weight
measureFromConst "rank" = Just Rank
measureFromConst _ = Nothing

potForMeasure :: Measure -> A.PotentialKind
potForMeasure Weight = A.Weight
potForMeasure Rank = A.Rank

data Predicate = Predicate Measure PredOp Id Id [Constraint] Type
  deriving (Eq, Ord, Show)

predApplySubst :: Substitution -> Predicate -> Predicate
predApplySubst s (Predicate m op x y p t) = Predicate m op (applySubst s x) (applySubst s y) p t

predVars :: Predicate -> Set Id
predVars (Predicate _ _ x y _ _) = S.fromList [x,y]

hasVars :: Set Id -> Predicate -> Bool
hasVars vars p = not . S.null $ predVars p `S.intersection` vars

hasOnlyVars :: Set Id -> Predicate -> Bool
hasOnlyVars vars p = predVars p `S.isSubsetOf` vars

excludeByVars :: Set Predicate -> Set Id -> Set Predicate
excludeByVars ps vars = S.filter (not . hasVars vars) ps

restrictByVars :: Set Predicate -> Set Id -> Set Predicate
restrictByVars ps vars = S.filter (hasOnlyVars vars) ps

measure ::  PositionedExpr -> Maybe (Measure, Id)
measure (Const c [Var x]) = do
  m <- measureFromConst c
  return (m,x)
measure _ = Nothing

predFromCondition :: PositionedExpr -> Maybe Predicate
predFromCondition = predFromCondition' M.empty

predFromCondition' :: Map Id PositionedExpr -> PositionedExpr -> Maybe Predicate
predFromCondition' env (Let x e1 e2) = predFromCondition' (M.insert x e1 env) e2
predFromCondition' env (Const op args) = do
  args' <- mapM (env M.!?) =<< mapM toVar args
  constToPredicate op args'
predFromCondition' _ _ = Nothing

constToPredicate :: Id -> [PositionedExpr] -> Maybe Predicate
constToPredicate "EQ" args = buildPredicate Eq args
constToPredicate "LE" args = buildPredicate Le args
constToPredicate "LT" args = buildPredicate Lt args
constToPredicate "GE" [x,y] = buildPredicate Le [y,x]
constToPredicate "GT" [x,y] = buildPredicate Lt [y,x]
constToPredicate _ _ = Nothing

buildPredicate :: PredOp -> [PositionedExpr] -> Maybe Predicate
buildPredicate op [arg1, arg2] = do
  (m1, x) <- measure arg1
  let t1 = getType arg1
  (m2, y) <- measure arg2
  let t2 = getType arg2
  guard (m1 == m2)
  guard (t1 == t2)
  return (Predicate m1 op x y [] t1)

negate :: Predicate -> Predicate
negate (Predicate m Eq x y p t) = Predicate m Neq x y p t
negate (Predicate m Neq x y p t) = Predicate m Eq x y p t
negate (Predicate m Le x y p t) = Predicate m Lt y x p t
negate (Predicate m Lt x y p t) = Predicate m Le y x p t

anyImplies :: Set Predicate -> Predicate -> (Bool, [Constraint])
anyImplies ps p = let (b, cs) = foldr (go . (`implies` p)) (False, []) ps in
  (b, or cs)
  where go (b, t) (acc, cs) = (b || acc, t ++ cs)

implies :: Predicate -> Predicate -> (Bool, [Constraint])
implies (Predicate m1 op1 x1 y1 p _) (Predicate m2 op2 x2 y2 _ _)
  | m1 == m2 && op1 == op2 && x1 == x2 && y1 == y2 = (True, p)
implies (Predicate m1 Eq x1 y1 p _) (Predicate m2 Le x2 y2 _ _)
  | m1 == m2 && x1 == x2 && y1 == y2 = (True, p)
implies (Predicate m1 Lt x1 y1 p _) (Predicate m2 Le x2 y2 _ _) 
  | m1 == m2 && x1 == x2 && y1 == y2 = (True, p)
implies _ _ = (False, [])

