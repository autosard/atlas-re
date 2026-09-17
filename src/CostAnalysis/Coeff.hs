{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}



module CostAnalysis.Coeff
  ( Coeff (..)
  , HasCoeffs (..)
  , printCoeff
  , instCoeffs
  )where

import Data.Map (Map)
import qualified Data.Map as M


import Syntax.ResourceExpression

data Coeff =
  Coeff
    Int -- ^ Unique identifier for the annotation; used together with coefficent index to identify coeffients when encoding them for smt. 
    ResourceTerm -- ^ An index to identify the coefficient.
  deriving (Eq, Ord, Show)

printCoeff :: Coeff -> String
printCoeff (Coeff id t) = show id ++ "[" ++ show t ++ "]" 

class HasCoeffs a where
  getCoeffs :: a -> [Coeff]

instance HasCoeffs a => HasCoeffs [a] where
  getCoeffs = concatMap getCoeffs

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
  
instCoeffs :: Map Coeff Rational -> ResourceExpr -> ResourceExpr
instCoeffs vals = M.map go
  where go :: RScalar -> RScalar
        go (RSConst k) = RSConst k
        go (RSCoeff i idx)
          | M.member (Coeff i idx) vals = RSConst (vals M.! Coeff i idx)
          | otherwise = RSCoeff i idx
        go (RSAdd s1 s2) = RSAdd (go s1) (go s2)
        go (RSMul s1 s2) = RSMul (go s1) (go s2) 
