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

data RsrcAnn = RsrcAnn {
  -- | Number of tree arguments
  --len :: Int,
  -- | Tree args
  args :: [(Id, Type)],
  -- | Map of variables to coefficients
  coeffs :: CoeffsMap}
  deriving (Eq, Show)

annVars :: RsrcAnn -> [Id]
annVars = map fst . args

class Index a where
  infixl 9 !
  (!) :: RsrcAnn -> a -> Coeff

instance Index Id where
  (!) ann@(RsrcAnn _ coeffs) x = case M.lookup (Pure x) coeffs of
    Just c -> c
    Nothing -> error $ "Invalid index '" ++ unpack x ++ "' for annotation '" ++ show ann ++ "'."

instance Index [Factor] where
  (!) :: RsrcAnn -> [Factor] -> Coeff
  (!) ann factors = ann!S.fromList factors

factorGTZero :: Factor -> Bool
factorGTZero (Arg _ a) = a > 0
factorGTZero (Const c) = c > 0

instance Index (Set Factor) where
  (!) :: RsrcAnn -> Set Factor -> Coeff
  (!) ann@(RsrcAnn _ coeffs) factors =
    let factors' = S.filter factorGTZero factors in
      case M.lookup (Mixed factors') coeffs of
        Just c -> c
        Nothing -> error $ "Invalid index '" ++ show factors ++ "' for annotation '" ++ show ann ++ "'."

type AnnArray = Map (Set Factor) RsrcAnn

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

--calculateBound :: Id -> RsrcSignature -> Map Coeff Rational -> [Coeff]
--calculateBound 

class HasCoeffs a where
  getCoeffs :: a -> [Coeff]

instance HasCoeffs CoeffsMap where
  getCoeffs = M.elems

instance HasCoeffs [CoeffsMap] where
  getCoeffs = concatMap M.elems  

instance HasCoeffs RsrcAnn where
  getCoeffs = getCoeffs . coeffs

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
  
instance HasCoeffs FunRsrcAnn where
  getCoeffs ann = (getCoeffs . withCost) ann ++ (getCoeffs . withoutCost) ann

instance HasCoeffs RsrcSignature where
  getCoeffs = concatMap getCoeffs . M.elems
