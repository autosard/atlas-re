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
import Syntax.ResourceExpression.Size

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
type Subst = M.Map SizeVar SizeSum


unify :: TermPattern -> ResourceTerm -> Subst -> [Subst]
unify PId RTId subst = [subst]
unify (PGenLog pTerms) (RTLog rTerms) subst = do
  -- Find all possible ways to group the concrete terms to match the pattern terms
  partitionedTerms <- partitionsK (length pTerms) rTerms
  unifySizeList pTerms partitionedTerms subst
unify _ _ _ = []

-- | Unifies a list of size patterns with grouped size terms
unifySizeList :: [SizeVar] -> [SizeSum] -> Subst -> [Subst]
unifySizeList [] [] subst = [subst]
unifySizeList (p:ps) (r:rs) subst = do
  nextSubst <- unifySizeVar p r subst
  unifySizeList ps rs nextSubst
unifySizeList _ _ _ = []

-- | Unifies a size pattern with a sum of concrete size terms
unifySizeVar :: SizeVar -> SizeSum -> Subst -> [Subst]
unifySizeVar v concreteTerms subst =
  case M.lookup v subst of
    Just boundTerms -> do
      guard (boundTerms == concreteTerms)
      return subst
    Nothing -> return (M.insert v concreteTerms subst)



partitionsK :: Int -> SizeSum -> [[SizeSum]]
partitionsK k (SizeSum cs constVal) = do
  let varTerms = [VarTerm v c | (v, c) <- M.toList cs, c /= 0]
      cTerm    = [ConstTerm constVal | constVal /= 0]
      allTerms = varTerms ++ cTerm
  partitions <- partitions allTerms
  
  return (map sizeFromList partitions)

partitions :: [a] -> [[[a]]]
partitions [x] = [[[x]]]
partitions (x:xs) =
  let ys = partitions xs in
    [[x] : y | y <- ys]
    ++ concatMap (multiply x) ys
  where multiply :: a -> [[a]] -> [[[a]]]
        multiply x [y] = [[(x : y)]]
        multiply x (y:ys) = ((x : y) : ys) : map (y:) (multiply x ys)


-- | Non-deterministically matches a sequence of patterns against the active term set
findMatches :: [TermPattern] -> [ResourceTerm] -> Subst -> [[ResourceTerm]]
findMatches [] _ _ = [[]]
findMatches (p:ps) allTerms subst = do
  term      <- allTerms
  nextSubst <- unify p term subst
  rest      <- findMatches ps allTerms nextSubst
  return (term : rest)
