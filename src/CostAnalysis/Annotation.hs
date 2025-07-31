{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}

module CostAnalysis.Annotation where

import Prelude hiding (zipWith)
import qualified Prelude as P
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Map.Merge.Strict as Merge(merge, zipWithMatched, mapMissing)
import Control.Monad.State
import Lens.Micro.Platform hiding (to)

import Primitive(Id, Substitution)
import CostAnalysis.Template (Template,
                              TermTemplate,
                              BoundTemplate,
                              FreeTemplate(..),
                              CoeffDef,
                              zeroTemplate)
import qualified CostAnalysis.Template as Templ
import CostAnalysis.Constraint
import qualified CostAnalysis.Constraint as C
import Typing.Type
import CostAnalysis.Coeff


type Ann a = Map Type a

type FreeAnn = Ann FreeTemplate
type BoundAnn = Ann BoundTemplate

zeroAnnFrom :: (Template a) => Ann a -> BoundAnn
zeroAnnFrom = M.map go
  where go t = Templ.BoundTemplate (Templ.args t) $
          M.fromList [(q, 0) | q <- S.toList $ Templ.idxs t]

annArgs :: (Template a) => Ann a -> [Id]
annArgs qs = concatMap Templ.args (M.elems qs)

instance HasCoeffs FreeAnn where
  getCoeffs = M.foldr (\q coeffs -> coeffs ++ getCoeffs q) []

merge :: (Template a) => Ann a -> Ann a -> Ann a
merge = M.unionWith Templ.merge

split :: BoundAnn -> BoundAnn -> (BoundAnn, BoundAnn)
split qs ps = foldr go (M.empty, M.empty) $ M.assocs qs
  where go (t, q) (xs, ys) = let args' = maybe [] Templ.args (ps M.!? t)
                                 (x, y) = Templ.split q args' in
                               (M.insert t x xs, M.insert t y ys)

zipWith :: (Type -> a -> c) -> (Type -> b -> c) -> (Type -> a -> b -> c) -> Ann a -> Ann b -> Ann c
zipWith fL fR zipper = Merge.merge missingStrategyL missingStrategyR (Merge.zipWithMatched zipper)
  where missingStrategyL = Merge.mapMissing fL
        missingStrategyR = Merge.mapMissing fR

scale :: (Template a) => Ann a -> Term -> Ann TermTemplate
scale qs k = M.map (`Templ.scale` k) qs

add :: (Template a, Template b) => Ann a -> Ann b -> Ann TermTemplate
add = zipWith
  (const (`Templ.add` zeroTemplate))
  (const (Templ.add zeroTemplate))
  (const Templ.add)

sub :: (Template a, Template b) => Ann a -> Ann b -> Ann TermTemplate
sub = zipWith
  (const (`Templ.sub` zeroTemplate))
  (const (Templ.sub zeroTemplate))
  (const Templ.sub)

sum :: (Template a) => Ann a -> Term
sum q = C.sum . M.elems $  M.map Templ.sum q

symbolicCost :: (Template a, Template b) => ((Ann a, Ann a), Ann b) -> Ann TermTemplate
symbolicCost ((from, fromRef), to)
  = let diff = zipWith
               (const (`Templ.symbolicCost` zeroTemplate))
               (const (Templ.symbolicCost zeroTemplate))
               (const Templ.symbolicCost) from to in
      add diff fromRef


assertEq :: (Template a, Template b) => Ann a -> Ann b -> [Constraint]
assertEq qs ps = concat . M.elems $ zipWith
  (const (`Templ.assertEq` zeroTemplate))
  (const (Templ.assertEq zeroTemplate))
  (const Templ.assertEq) qs ps

assertLe :: (Template a, Template b) => Ann a -> Ann b -> [Constraint]
assertLe qs ps = concat . M.elems $ zipWith
  (const (`Templ.assertLe` zeroTemplate))
  (const (Templ.assertLe zeroTemplate))
  (const Templ.assertLe) qs ps

assertGeZero :: (Template a) => Ann a -> [Constraint]
assertGeZero = M.foldr go []
  where go templ cs = cs ++ Templ.assertGeZero templ

assertZero :: (Template a) => Ann a -> [Constraint]
assertZero = M.foldr go []
  where go templ cs = cs ++ Templ.assertZero templ

assertZeroExcept :: (Template a) => Ann a -> Type -> [CoeffIdx] -> [Constraint]
assertZeroExcept qs tExcept idxs = foldr go [] (M.assocs qs)
  where go (t, templ) cs = if t == tExcept
                           then Templ.assertZeroExcept templ (S.fromList idxs)
                           else Templ.assertZero templ

unifyAssertEq :: (Template a, Template b) => Ann a -> Ann b -> [Constraint]
unifyAssertEq qs ps = concat . M.elems $ zipWith
  (const (`Templ.unifyAssertEq` zeroTemplate))
  (const (Templ.unifyAssertEq zeroTemplate))
  (const Templ.unifyAssertEq) qs ps

unifyAssertEqBy :: (Template a, Template b) => Ann a -> Ann b -> Map Type [Id] -> [Constraint]
unifyAssertEqBy qs ps' args = concat . M.elems $ zipWith
  (\t q -> unifyForType t q zeroTemplate)
  (`unifyForType` zeroTemplate)
  unifyForType qs ps'
  where unifyForType :: (Template a, Template b) => Type -> a -> b -> [Constraint]
        unifyForType t q p = Templ.unifyAssertEqBy q p (args M.! t)

extend :: FreeAnn -> CoeffDef FreeAnn [a] -> (FreeAnn, [a])
extend ann def = (ann', cs)
  where (cs, ann') = runState def ann

defMulti :: Index i => [(Type, i)] -> CoeffDef FreeAnn [Term]
defMulti = mapM go
  where go :: Index i => (Type, i) -> CoeffDef FreeAnn Term
        go (t, i) = do
          let idx = toIdx i
          ix t . Templ.ftCoeffs %= (idx `S.insert`)
          templ <- gets (M.! t) 
          return $  templ Templ.! idx

defineByWith :: FreeAnn -> FreeAnn -> (Type -> CoeffIdx -> Term -> Term -> [Constraint]) -> (FreeAnn, [Constraint])
defineByWith qs ps_ f = foldr go (M.empty, []) (M.keys ps_)
  where go :: Type -> (FreeAnn, [Constraint]) -> (FreeAnn, [Constraint])
        go t (ps, css) = let (p, cs) = Templ.defineByWith (qs M.! t) (ps_ M.! t) (f t) in
                           (M.insert t p ps, css ++ cs)

defineBy :: FreeAnn -> FreeAnn -> (FreeAnn, [Constraint])
defineBy qs ps = defineByWith qs ps (const . const eq)

data ProveKind = Upper | Lower
  deriving(Eq, Ord, Show)

data FunSig a = FunSig {
  from :: (Ann a, Ann a),
  to :: Ann a}
  deriving(Eq, Show)

type FreeFunSig = FunSig FreeTemplate

data Measure = Weight
  deriving(Eq, Ord, Show)

data (Template a) => FunAnn a = FunAnn {
  withCost :: FunSig a,
  withoutCost :: [FunSig a],
  aux :: Map (Measure, ProveKind) (FunSig a),
  worstCase :: Bool}
  deriving(Eq, Show)

assertFunAnnEq :: (Template a, Template b) => FunAnn a -> FunAnn b -> [Constraint]
assertFunAnnEq q p = 
  assertSigEq (withCost q) (withCost p)
  ++ concat (P.zipWith assertSigEq (withoutCost q) (withoutCost p))
  where assertSigEq x y = 
          assertEq (fst . from $ x) (fst . from $ y)
          ++ assertEq (snd . from $ x) (snd . from $ y)
          ++ assertEq (to x) (to y)



type FreeFunAnn = FunAnn FreeTemplate

instance HasCoeffs (FunSig FreeTemplate) where
  getCoeffs ann = getCoeffs (from ann)
    ++ getCoeffs (to ann)

instance HasCoeffs FreeFunAnn where
  getCoeffs ann = getCoeffs (withCost ann)
    ++ getCoeffs (withoutCost ann)
    

type BoundFunAnn = FunAnn BoundTemplate

type AnnSignature a = Map Id (FunAnn a)

instance HasCoeffs FreeSignature where
  getCoeffs = concatMap getCoeffs . M.elems


type FreeSignature = Map Id FreeFunAnn
type BoundSignature = Map Id BoundFunAnn

share :: FreeAnn -> FreeAnn -> [Id] -> Substitution -> Substitution -> (FreeAnn, [Constraint])
share qs ps_ zs s1 s2 = foldr go (M.empty, []) (M.keys ps_)
  where go :: Type -> (FreeAnn, [Constraint]) -> (FreeAnn, [Constraint])
        go t (ps, css) = let (p, cs) = Templ.share (qs M.! t) (ps_ M.! t) zs s1 s2 in
                           (M.insert t p ps, css ++ cs)


