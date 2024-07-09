{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module CostAnalysis.RsrcAnn where

import Data.Text(unpack)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Coeff
import Typing.Type

data HasCoeffs a => RsrcAnn a = RsrcAnn {
  -- | Number of tree arguments
  --len :: Int,
  -- | Tree args
  args :: [(Id, Type)],
  -- | Map of variables to coefficients
  coeffs :: a}
  deriving (Eq, Show)

annVars :: HasCoeffs a => RsrcAnn a -> [Id]
annVars = map fst . args

type GroundAnn = RsrcAnn CoeffsMap
type CombinedAnn = RsrcAnn [CoeffsMap]

class Index a where
  infixl 9 !
  (!) :: GroundAnn -> a -> Coeff

instance Index Id where
  (!) ann@(RsrcAnn _ coeffs) x = case M.lookup (Pure x) coeffs of
    Just c -> c
    Nothing -> error $ "Invalid index '" ++ unpack x ++ "' for annotation '" ++ show ann ++ "'."

instance Index [Factor] where
  (!) :: GroundAnn -> [Factor] -> Coeff
  (!) ann factors = ann!S.fromList factors

factorGTZero :: Factor -> Bool
factorGTZero (Arg _ a) = a > 0
factorGTZero (Const c) = c > 0

instance Index (Set Factor) where
  (!) :: GroundAnn -> Set Factor -> Coeff
  (!) ann@(RsrcAnn _ coeffs) factors =
    let factors' = S.filter factorGTZero factors in
      case M.lookup (Mixed factors') coeffs of
        Just c -> c
        Nothing -> error $ "Invalid index '" ++ show factors ++ "' for annotation '" ++ show ann ++ "'."

type family AnnArray a


type instance AnnArray GroundAnn = Map (Set Factor) GroundAnn
type instance AnnArray CombinedAnn = [Map (Set Factor) GroundAnn]

infixl 9 !!
(!!) :: AnnArray GroundAnn -> Set Factor -> GroundAnn
(!!) arr k = let k' = S.filter factorGTZero k in
    case M.lookup k' arr of
      Just c -> c
      Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation array."


data FunRsrcAnn a = FunRsrcAnn {
  withCost :: (RsrcAnn a, RsrcAnn a),
  withoutCost :: (RsrcAnn a, RsrcAnn a)}
  deriving(Show)

type RsrcSignature a = Map Id (FunRsrcAnn a)

class HasCoeffs a where
  getCoeffs :: a -> [Coeff]

instance HasCoeffs CoeffsMap where
  getCoeffs = M.elems

instance HasCoeffs [CoeffsMap] where
  getCoeffs = concatMap M.elems  

instance HasCoeffs a => HasCoeffs (RsrcAnn a) where
  getCoeffs = getCoeffs . coeffs

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
  
instance HasCoeffs a => HasCoeffs (FunRsrcAnn a) where
  getCoeffs ann = (getCoeffs . withCost) ann ++ (getCoeffs . withoutCost) ann

instance HasCoeffs a => HasCoeffs (RsrcSignature a) where
  getCoeffs = concatMap getCoeffs . M.elems
