module Syntax.ResourceExpression.Pattern
  ( PatVar (..)
  , SizePattern (..)
  , TermPattern (..)
  , SizeTermPattern (..)
  , IneqPattern (..)
  , ResourcePattern
  , unify
  , findMatches
  , SizeSubst
  , instResourceIneq
  )where

import qualified Data.Map.Strict as M
import Control.Monad (guard)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
import qualified Data.Set as S
import Data.Maybe (mapMaybe)

import Syntax (Id, HasVars (..), HasProduct (..), normalisedProd)
import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM
import Syntax.FreeModule (FreeModule)
import qualified Syntax.ResourceExpression.Inequality as ReIneq (ResourceIneq (..))

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
  = TPVar Id
  | TPLog SizePattern
  | TPPhi Id
  | TPBinom SizePattern Int
  | TPProd (MultiSet TermPattern)
  | TPId
  deriving (Eq, Ord, Show)

type ResourcePattern = FreeModule TermPattern Rational

instance HasProduct TermPattern where
  one = TPId
  prod = TPProd
  unprod (TPProd ts) = Just ts
  unprod otherTerm   = Nothing

instance Semigroup TermPattern where
  (<>) = normalisedProd

instance Monoid TermPattern where
  mempty = TPId

newtype IneqPattern = LeZero ResourcePattern
  deriving (Eq, Show, Ord)

-- | Substitutions map pattern variables to a sum of concrete size terms
type SizeSubst = M.Map Id SizeExpr


unify :: TermPattern -> ResourceTerm -> SizeSubst -> [SizeSubst]
unify (TPVar x) (RTSize y) subst = unifySizeVar (x,1) (FM.singleton (SVar y)) subst
unify TPId RTId subst = [subst]
unify (TPLog s1) (RTLog s2) subst = unifySizePattern s1 s2 subst
unify (TPBinom s1 k1) (RTBinom s2 k2) subst | k1 == k2 = unifySizePattern s1 s2 subst
unify _ _ _ = []

unifySizePattern :: SizePattern -> SizeExpr -> SizeSubst -> [SizeSubst]
unifySizePattern p s subst = do
  let c = M.findWithDefault 0 SPId  p
      d = M.findWithDefault 0 SId s
      s' = M.adjust (const (c-d)) SId s
      pVars = mapMaybe toVar $ M.toList p
  partitionedTerms <- FM.partitions (length pVars) s'
  unifySizeVars pVars partitionedTerms subst
  where toVar (SPVar x, k) = Just (x, k)
        toVar (SPId, _) = Nothing
                         
unifySizeVars :: [(Id, Rational)] -> [SizeExpr] -> SizeSubst -> [SizeSubst]
unifySizeVars [] [] subst = [subst]
unifySizeVars (p:ps) (r:rs) subst = do
  nextSizeSubst <- unifySizeVar p r subst
  unifySizeVars ps rs nextSizeSubst
unifySizeVars _ _ _ = []
                           
unifySizeVar :: (Id, Rational) -> SizeExpr -> SizeSubst -> [SizeSubst]
unifySizeVar (v, k) concreteTerms subst =
  let st = FM.scale (1/k) concreteTerms in
  case M.lookup v subst of
    Just boundTerms -> do
      guard (boundTerms == st)
      return subst
    Nothing -> return (M.insert v st subst)

-- | Non-deterministically matches a sequence of patterns against the active term set
findMatches :: ResourcePattern -> [ResourceTerm]
           -> [([(ResourceTerm, Rational)], SizeSubst)]
findMatches rp ts = go (M.toList rp) ts M.empty
  where
    go [] _ subst = [([], subst)]
    go ((p, k):ps) allTerms subst = do
      term            <- allTerms
      nextSubst       <- unify p term subst
      (rest, finalSubst) <- go ps allTerms nextSubst
      return ((term, k) : rest, finalSubst)

instResourceIneq :: SizeSubst -> IneqPattern -> ReIneq.ResourceIneq
instResourceIneq s (LeZero rp) =  ReIneq.LeZero (instPattern s rp)

instPattern :: SizeSubst -> ResourcePattern -> RatResourceExpr
instPattern s = FM.linMap (instTermPattern s)

instTermPattern :: SizeSubst -> TermPattern -> RatResourceExpr
instTermPattern s (TPVar x) = FM.map fromSizeTerm (s M.! x)
instTermPattern s (TPLog sp) = FM.singleton $ RTLog $ instSizePattern s sp
instTermPattern s (TPPhi x) = FM.singleton $ RTPhi x
instTermPattern s (TPBinom sp k) = FM.singleton $ RTBinom (instSizePattern s sp) k
instTermPattern s (TPProd ts) = FM.prod $ map (instTermPattern s) $ MSet.toList ts
instTermPattern s TPId = FM.singleton RTId

instSizePattern :: SizeSubst -> SizePattern -> SizeExpr
instSizePattern s = FM.linMap (instSizeTermPattern s)
  
instSizeTermPattern :: SizeSubst -> SizeTermPattern -> SizeExpr
instSizeTermPattern s SPId = FM.singleton SId
instSizeTermPattern s (SPVar x) = s M.! x 

