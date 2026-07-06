{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax.Measure where

import qualified Data.Kind (Type)
import Data.List (find)

import Primitive(Id)
import Syntax.ResourceExpression
import Typing.Type

data ConstPat = ConstPat Id [Id]
  deriving Show
data ConstValue a = ConstValue Id [a]
  deriving Show

data Measure = Size | Potential
  deriving Show

type family Carrier (m :: Measure) :: Data.Kind.Type where
  Carrier 'Size      = [SizeTerm]
  Carrier 'Potential = [ResourceTerm]
  

newtype MeasureAlgebra (m :: Measure) = Equations [(ConstPat, Carrier m)]

deriving instance Show (Carrier m) => Show (MeasureAlgebra m)


data MeasureEnv = MeasureEnv {
  sizeMeasure :: MeasureAlgebra Size,
  potentialMeasure :: MeasureAlgebra Potential
} deriving Show

-- apply :: MeasureAlgebra a -> ConstValue a -> a
-- apply (Equations eq) cv = case find (match cv . fst) eqs of
--         Just (_, result) -> result
--         Nothing          -> error "No matching equation in F-Algebra."

-- match :: ConstValue a -> ConstPat -> Bool
-- match (ConstValue c2 vs) (ConstPat c1 xs) = c1 == c2 && length xs == length vs 

-- reduceSize :: TypeCtx -> MeasureEnv -> Substitution
