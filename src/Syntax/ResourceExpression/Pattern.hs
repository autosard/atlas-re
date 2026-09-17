module Syntax.ResourceExpression.Pattern
  ( PatVar (..)
  , SizeVar (..)
  , SizePattern (..)
  , TermPattern (..)
  , unify
  , findMatches
  )where

import qualified Data.Map.Strict as M
import Control.Monad (guard)

import Syntax (Id)
import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM

newtype PatVar = PatVar Id deriving (Eq, Ord, Show)
newtype SizeVar = SizeVar Id deriving (Eq, Ord, Show)

-- | Patterns for sizes (can match a sub-sum of size terms)
data SizePattern
  = SPVar PatVar
  | SPConst Int
  deriving (Eq, Ord, Show)

-- | Patterns for full resource terms
data TermPattern
  = PGenLog [SizeVar]
  | PLog [SizePattern]
  | PPhi PatVar
  | PId
  deriving (Eq, Ord, Show)

-- | Substitutions map pattern variables to a sum of concrete size terms
type Subst = M.Map SizeVar SizeExpr


unify :: TermPattern -> ResourceTerm -> Subst -> [Subst]
unify PId RTId subst = [subst]
unify (PGenLog pTerms) (RTLog rTerms) subst = do
  partitionedTerms <- FM.partitions (length pTerms) rTerms
  unifySizeList pTerms partitionedTerms subst
unify _ _ _ = []

-- | Unifies a list of size patterns with grouped size terms
unifySizeList :: [SizeVar] -> [SizeExpr] -> Subst -> [Subst]
unifySizeList [] [] subst = [subst]
unifySizeList (p:ps) (r:rs) subst = do
  nextSubst <- unifySizeVar p r subst
  unifySizeList ps rs nextSubst
unifySizeList _ _ _ = []

-- | Unifies a size pattern with a sum of concrete size terms
unifySizeVar :: SizeVar -> SizeExpr -> Subst -> [Subst]
unifySizeVar v concreteTerms subst =
  case M.lookup v subst of
    Just boundTerms -> do
      guard (boundTerms == concreteTerms)
      return subst
    Nothing -> return (M.insert v concreteTerms subst)

-- | Non-deterministically matches a sequence of patterns against the active term set
findMatches :: [TermPattern] -> [ResourceTerm] -> Subst -> [[ResourceTerm]]
findMatches [] _ _ = [[]]
findMatches (p:ps) allTerms subst = do
  term      <- allTerms
  nextSubst <- unify p term subst
  rest      <- findMatches ps allTerms nextSubst
  return (term : rest)
