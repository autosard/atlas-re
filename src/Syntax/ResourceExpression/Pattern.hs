module Syntax.ResourceExpression.Pattern where

import qualified Data.Map.Strict as M
import Control.Monad (guard)

import Primitive(Id)
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
  -- 1. Extract indivisible terms (drop 0-valued terms)
  let varTerms = [VarTerm v c | (v, c) <- M.toList cs, c /= 0]
      cTerm    = [ConstTerm constVal | constVal /= 0]
      allTerms = varTerms ++ cTerm
  -- 2. Distribute each indivisible term into one of the k buckets
  partitions <- partitions k allTerms
  
  return (map sizeFromList partitions)

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

-- | Non-deterministically matches a sequence of patterns against the active term set
findMatches :: [TermPattern] -> [ResourceTerm] -> Subst -> [[ResourceTerm]]
findMatches [] _ _ = [[]]
findMatches (p:ps) allTerms subst = do
  term      <- allTerms
  nextSubst <- unify p term subst
  rest      <- findMatches ps allTerms nextSubst
  return (term : rest)
