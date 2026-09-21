module Syntax.ResourceExpression.Pattern
  ( PatVar (..)
  , SizePattern (..)
  , TermPattern (..)
  , SizeTermPattern (..)
  , IneqPattern (..)
  , unify
  , findMatches
  )where

import qualified Data.Map.Strict as M
import Control.Monad (guard)
import Data.MultiSet (MultiSet)
import qualified Data.Set as S
import Data.Maybe (mapMaybe)

import Syntax (Id, HasVars (..))
import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM
import Syntax.FreeModule (FreeModule)

newtype PatVar = PatVar Id deriving (Eq, Ord, Show)


-- | Patterns for sizes (can match a sub-sum of size terms)
data SizeTermPattern
  = SPId
  | SPVar Id
  deriving (Eq, Ord, Show)

instance HasVars SizeTermPattern where
  freeVars (SPVar x) = S.singleton x
  freeVars SPId      = S.empty

type SizePattern = FreeModule SizeTermPattern Rational

-- | Patterns for full resource terms
data TermPattern
  = TPSize SizePattern
  | TPLog SizePattern
  | TPPhi Id
  | TPBinom SizePattern Int
  | RTProd (MultiSet TermPattern)
  | PVar Id
  | TPId
  deriving (Eq, Ord, Show)

type ResourceExprPattern = FreeModule TermPattern Rational

newtype IneqPattern = LeZero ResourceExprPattern

-- | Substitutions map pattern variables to a sum of concrete size terms
type Subst = M.Map Id SizeExpr


unify :: TermPattern -> ResourceTerm -> Subst -> [Subst]
unify TPId RTId subst = [subst]
unify (TPLog s1) (RTLog s2) subst = unifySizePattern s1 s2 subst
unify (TPBinom s1 k1) (RTBinom s2 k2) subst | k1 == k2 = unifySizePattern s1 s2 subst
unify _ _ _ = []

unifySizePattern :: SizePattern -> SizeExpr -> Subst -> [Subst]
unifySizePattern p s subst = do
  let c = M.findWithDefault 0 SPId  p
      d = M.findWithDefault 0 SId s
      s' = M.adjust (const (c-d)) SId s
      pVars = mapMaybe toVar $ M.toList p
  partitionedTerms <- FM.partitions (length pVars) s'
  unifySizeVars pVars partitionedTerms subst
  where toVar (SPVar x, k) = Just (x, k)
        toVar (SPId, _) = Nothing
                         
unifySizeVars :: [(Id, Rational)] -> [SizeExpr] -> Subst -> [Subst]
unifySizeVars [] [] subst = [subst]
unifySizeVars (p:ps) (r:rs) subst = do
  nextSubst <- unifySizeVar p r subst
  unifySizeVars ps rs nextSubst
unifySizeVars _ _ _ = []
                           
unifySizeVar :: (Id, Rational) -> SizeExpr -> Subst -> [Subst]
unifySizeVar (v, k) concreteTerms subst =
  let st = FM.scale (1/k) concreteTerms in
  case M.lookup v subst of
    Just boundTerms -> do
      guard (boundTerms == st)
      return subst
    Nothing -> return (M.insert v st subst)

-- | Non-deterministically matches a sequence of patterns against the active term set
findMatches :: ResourceExprPattern -> [ResourceTerm] -> [[(ResourceTerm, Rational)]]
findMatches rp ts = go (M.toList rp) ts M.empty
  where go [] _ _ = [[]]
        go ((p, k):ps) allTerms subst = do
          term      <- allTerms
          nextSubst <- unify p term subst
          rest      <- go ps allTerms nextSubst
          return ((term, k) : rest)
