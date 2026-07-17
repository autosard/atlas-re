module Syntax.ResourceExpression.Pattern where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad (guard)
import Data.List (permutations)

import Primitive(Id)
import Syntax.ResourceExpression

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
type Subst = M.Map SizeVar [SizeTerm]


unify :: TermPattern -> ResourceTerm -> Subst -> [Subst]
unify PId RTId subst = [subst]
unify (PGenLog pTerms) (RTLog rTerms) subst = do
  -- Find all possible ways to group the concrete terms to match the pattern terms
  partitionedTerms <- allPartitions (length pTerms) rTerms
  unifySizeList pTerms partitionedTerms subst
unify _ _ _ = []

-- | Unifies a list of size patterns with grouped size terms
unifySizeList :: [SizeVar] -> [[SizeTerm]] -> Subst -> [Subst]
unifySizeList [] [] subst = [subst]
unifySizeList (p:ps) (r:rs) subst = do
  nextSubst <- unifySizeVar p r subst
  unifySizeList ps rs nextSubst
unifySizeList _ _ _ = []

-- | Unifies a size pattern with a sum of concrete size terms
unifySizeVar :: SizeVar -> [SizeTerm] -> Subst -> [Subst]
unifySizeVar v concreteTerms subst =
  case M.lookup v subst of
    Just boundTerms -> do
      guard (S.fromList boundTerms == S.fromList concreteTerms)
      return subst
    Nothing -> return (M.insert v concreteTerms subst)

-- | Partitions a list of elements into k non-empty sublists in all possible ways.
-- Example: partitions 2 [t, u] -> [([[t], [u]]), ([[u], [t]])]
partitions :: Int -> [a] -> [[[a]]]
partitions 1 xs = [[xs]]
partitions k xs 
  | k <= 0 || null xs = []
  | k > length xs     = []
  | otherwise         = do
      -- Pick a non-empty prefix for the first group (using permutations to handle any ordering)
      (part, rest) <- splits xs
      nextParts    <- partitions (k - 1) rest
      return (part : nextParts)
  where
    -- Helper to get all non-empty splits of a list
    splits []     = []
    splits (y:ys) = ([y], ys) : map (\(p, r) -> (y:p, r)) (splits ys)

-- | Generates all permutations of partitions to cover commutative matches.
allPartitions :: Int -> [a] -> [[[a]]]
allPartitions k xs = concatMap (partitions k) (permutations xs)

-- | Non-deterministically matches a sequence of patterns against the active term set
findMatches :: [TermPattern] -> [ResourceTerm] -> Subst -> [[ResourceTerm]]
findMatches [] _ _ = [[]]
findMatches (p:ps) allTerms subst = do
  term      <- allTerms
  nextSubst <- unify p term subst
  rest      <- findMatches ps allTerms nextSubst
  return (term : rest)
