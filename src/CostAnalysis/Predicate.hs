{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Predicate where

import Prelude hiding (or)

import Data.Set(Set)
import qualified Data.Map as M
import Data.Map(Map)

import Primitive(Id, Substitution, applySubst)
import Ast 
import Control.Monad (guard)
import qualified Data.Set as S
import CostAnalysis.Constraint (Term, or, Constraint (Atom))
import Data.Maybe (maybe, maybeToList)

data PredOp = Le | Lt | Eq | Neq
  deriving (Eq, Ord, Show)

data Predicate = Predicate Id PredOp Id Id (Maybe Term)
  deriving (Eq, Ord, Show)

predApplySubst :: Substitution -> Predicate -> Predicate
predApplySubst s (Predicate m op x y t) = Predicate m op (applySubst s x) (applySubst s y) t

predVars :: Predicate -> Set Id
predVars (Predicate _ _ x y _) = S.fromList [x,y]

hasVars :: Set Id -> Predicate -> Bool
hasVars vars p = not . S.null $ predVars p `S.intersection` vars

hasOnlyVars :: Set Id -> Predicate -> Bool
hasOnlyVars vars p = predVars p `S.isSubsetOf` vars

excludeByVars :: Set Predicate -> Set Id -> Set Predicate
excludeByVars ps vars = S.filter (not . hasVars vars) ps

restrictByVars :: Set Predicate -> Set Id -> Set Predicate
restrictByVars ps vars = S.filter (hasOnlyVars vars) ps

measure ::  PositionedExpr -> Maybe (Id, Id)
measure (Const m [Var x]) = Just (m,x)
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
  (m2, y) <- measure arg2
  guard (m1 == m2)
  return (Predicate m1 op x y Nothing)

negate :: Predicate -> Predicate
negate (Predicate m Eq x y t) = Predicate m Neq x y t
negate (Predicate m Neq x y t) = Predicate m Eq x y t
negate (Predicate m Le x y t) = Predicate m Lt y x t
negate (Predicate m Lt x y t) = Predicate m Le y x t

anyImplies :: Set Predicate -> Predicate -> (Bool, [Constraint])
anyImplies ps p = let (b, cs) = foldr (go . (`implies` p)) (False, cs) ps in
  (b, or cs)
  where go (b, t) (acc, cs) = (b || acc, (maybeToList . fmap Atom $ t) ++ cs)

implies :: Predicate -> Predicate -> (Bool, Maybe Term)
implies (Predicate m1 op1 x1 y1 t) (Predicate m2 op2 x2 y2 _)
  | m1 == m2 && op1 == op2 && x1 == x2 && y1 == y2 = (True, t)
implies (Predicate m1 Eq x1 y1 t) (Predicate m2 Le x2 y2 _)
  | m1 == m2 && x1 == x2 && y1 == y2 = (True, t)
implies (Predicate m1 Lt x1 y1 t) (Predicate m2 Le x2 y2 _) 
  | m1 == m2 && x1 == x2 && y1 == y2 = (True, t)
implies _ _ = (False, Nothing)

