{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

module Syntax.Measure where

import qualified Data.Kind (Type)

import Primitive(Id)
import Syntax.ResourceExpression

data ConstPat = ConstPat Id [Id]
  deriving (Eq, Show)
data ConstValue a = ConstValue Id [a]
  deriving Show

data Measure = Size | Potential
  deriving Show

type family Carrier (m :: Measure) :: Data.Kind.Type where
  Carrier 'Size      = [SizeTerm]
  Carrier 'Potential = [ResourceTerm]
  

newtype MeasureAlgebra (m :: Measure) = Equations [(ConstPat, Carrier m)]

deriving instance Show (Carrier m) => Show (MeasureAlgebra m)
deriving instance Eq (Carrier m) => Eq (MeasureAlgebra m)

data SMeasure (m :: Measure) where
  SSize      :: SMeasure 'Size
  SPotential :: SMeasure 'Potential


data MeasureEnv = MeasureEnv {
  sizeMeasure :: MeasureAlgebra Size,
  potentialMeasure :: Maybe (MeasureAlgebra Potential)
} deriving (Eq, Show)

-- apply :: MeasureAlgebra a -> ConstValue a -> a
-- apply (Equations eq) cv = case find (match cv . fst) eqs of
--         Just (_, result) -> result
--         Nothing          -> error "No matching equation in F-Algebra."

-- match :: ConstValue a -> ConstPat -> Bool
-- match (ConstValue c2 vs) (ConstPat c1 xs) = c1 == c2 && length xs == length vs 

-- reduceSize :: TypeCtx -> MeasureEnv -> Substitution
