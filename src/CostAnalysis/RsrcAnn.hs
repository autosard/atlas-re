{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.RsrcAnn where

import Prelude hiding (sum)

import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Data.Text(Text)
import Lens.Micro.Platform
import Data.Maybe (fromMaybe)


import Primitive(Id)
import CostAnalysis.Coeff
import Typing.Type
import Control.Monad.State
import CostAnalysis.Constraint


data RsrcAnn = RsrcAnn {
  _annId :: Int,
  _args :: [(Id, Type)],
  _label :: Text, -- ^ Human readable label, e.g. \"Q\", \"P\", ...
  _comment ::  Text, -- ^ Human readable comment, to trace the origin of the coefficient, e.g. "log".
  _coeffs :: Set CoeffIdx -- ^ non zero coefficients
  }
  deriving (Eq, Show)

makeLenses ''RsrcAnn

emptyAnn :: Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn
emptyAnn id label comment args = RsrcAnn id args label comment S.empty

fromAnn :: Int -> Text -> Text -> RsrcAnn -> RsrcAnn
fromAnn id label comment ann = RsrcAnn id (ann^.args) label comment (ann^.coeffs)

isPure :: CoeffIdx -> Bool
isPure (Pure _) = True
isPure _ = False

mixes :: RsrcAnn -> [CoeffIdx]
mixes ann = S.toList . S.filter (not . isPure) $ ann^.coeffs

pures :: RsrcAnn -> [CoeffIdx]
pures ann = S.toList . S.filter isPure $ ann^.coeffs


annVars :: RsrcAnn -> [Id]
annVars = map fst . _args

class AnnLike a where
  infixl 9 !
  (!) :: (Index i, Show i) => a -> i -> Term
  infixl 9 !?
  (!?) :: (Index i, Show i) => a -> i -> Term
  definedIdxs :: a -> Set CoeffIdx

instance AnnLike RsrcAnn where
  definedIdxs q = q^.coeffs
  (!) ann idx = case coeffForIdx ann (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> error $ "Invalid index '" ++ show idx ++ "' for annotation '" ++ show ann ++ "'."
  (!?) ann idx = case coeffForIdx ann (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> ConstTerm 0


class Index a where
  toIdx :: a -> CoeffIdx

coeffFromAnn :: RsrcAnn -> CoeffIdx -> Coeff
coeffFromAnn ann = Coeff (ann^.annId) (ann^.label) (ann^.comment)

coeffForIdx :: RsrcAnn -> CoeffIdx -> Maybe Coeff
coeffForIdx ann idx =
  if S.member idx (definedIdxs ann) then
    Just $ coeffFromAnn ann idx
  else Nothing

instance Index Id where
  toIdx = Pure

instance Index CoeffIdx where
  toIdx = id
    
instance Index [Factor] where
  toIdx = Mixed . S.fromList

factorGTZero :: Factor -> Bool
factorGTZero (Arg _ a) = a > 0
factorGTZero (Const c) = c > 0

instance Index (Set Factor) where
  toIdx factors = let factors' = S.filter factorGTZero factors in Mixed factors'

type PointWiseOp = Map CoeffIdx Term

instance AnnLike (Map CoeffIdx Term) where
  definedIdxs = M.keysSet
  (!) ann idx = ann M.! toIdx idx
  (!?) ann idx = fromMaybe (ConstTerm 0) $ ann M.!? toIdx idx

annScalarMul :: RsrcAnn -> Term -> PointWiseOp
annScalarMul q k = M.fromList [(idx, prod [q!idx, k]) | idx <- S.toList (q^.coeffs)]

annAdd :: RsrcAnn -> PointWiseOp -> PointWiseOp
annAdd q op = M.fromList
  [(idx, sum [q!?idx, op!?idx])
  | idx <- S.toList $ (q^.coeffs) `S.union` definedIdxs op]

annLikeEq :: (AnnLike a, AnnLike b) => a -> b -> [Constraint]
annLikeEq q op = concat [eq (q!?idx) (op!?idx)
             | idx <- S.toList $ definedIdxs op `S.union` definedIdxs op]

annEq :: RsrcAnn -> RsrcAnn -> [Constraint]
annEq q p | (length . _args $ q) /= (length . _args $ p) = error "Annotations with different lengths can not be equal."
          | otherwise = annLikeEq q p

type AnnArray = Map (Set Factor) RsrcAnn

elems :: AnnArray -> [RsrcAnn]
elems = M.elems

infixl 9 !!
(!!) :: AnnArray -> Set Factor -> RsrcAnn
(!!) arr k = let k' = S.filter factorGTZero k in
    case M.lookup k' arr of
      Just c -> c
      Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation array."


data FunRsrcAnn = FunRsrcAnn {
  withCost :: (RsrcAnn, RsrcAnn),
  withoutCost :: (RsrcAnn, RsrcAnn)}
  deriving(Show)

type RsrcSignature = Map Id FunRsrcAnn


type CoeffDef s a = State s a

def :: Index i => i -> CoeffDef RsrcAnn Term
def i = do
  let idx = toIdx i
  coeffs %= (idx `S.insert`)
  ann <- get
  return $ ann!idx

defEntry :: Set Factor -> CoeffIdx -> CoeffDef AnnArray Term
defEntry arrIdx coeffIdx = do
  ix arrIdx . coeffs %= (coeffIdx `S.insert`)
  arr <- get
  return $ (arr M.! arrIdx)!coeffIdx

extendAnn :: RsrcAnn -> [CoeffDef RsrcAnn [Constraint]] -> (RsrcAnn, [Constraint])
extendAnn ann defs = (ann', concat cs)
  where (cs, ann') = runState def ann
        def = sequence defs
        
extendAnns :: AnnArray -> [CoeffDef AnnArray [Constraint]] -> (AnnArray, [Constraint])
extendAnns arr defs = (arr', concat cs)
  where (cs, arr') = runState def arr
        def = sequence defs
                
instance HasCoeffs RsrcAnn where
  getCoeffs ann = map (coeffFromAnn ann) $ S.toList (ann^.coeffs)

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
  
instance HasCoeffs FunRsrcAnn where
  getCoeffs ann = (getCoeffs . withCost) ann ++ (getCoeffs . withoutCost) ann

instance HasCoeffs RsrcSignature where
  getCoeffs = concatMap getCoeffs . M.elems

  
