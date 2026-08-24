{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module CostAnalysis.Coeff
  ( Coeff (..)
  , HasCoeffs (..)
  , printCoeff
  )where

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
