{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StrictData #-}

module Syntax.Measure where

import Data.Kind (Type)
import Data.List (find)
import qualified Data.Set as S

import Primitive(Id, Substitutable(..), HasVars(..), substVars)
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size

data ConstPat = ConstPat Id [Id]
  deriving (Eq, Show)

instance HasVars ConstPat where
  freeVars (ConstPat _ vars) = S.fromList vars

data Measure = Size | Potential 
  deriving Show


type family Carrier (m :: Measure) :: Type 

type instance Carrier 'Size = SizeSum
type instance  Carrier 'Potential = [ResourceTerm]


data SizeTransform = SizeTransform {
  stLhs :: [Id]
  , stRhs :: SizeSum
  } deriving Show

applyST :: SizeTransform -> [Id] -> SizeSum
applyST st args = substVars (stLhs st) args (stRhs st)

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

apply :: (Show (Carrier a), Substitutable (Carrier a)) => MeasureAlgebra a -> ConstPat -> Carrier a
apply (Equations eqs) cv@(ConstPat _ argsInst) = case find (match cv . fst) eqs of
        Just (ConstPat _ argsDef, result) -> substVars argsDef argsInst result
        Nothing          -> error $ "No matching equation in F-Algebra." ++ show cv ++ show eqs

match :: ConstPat -> ConstPat -> Bool
match (ConstPat c2 xs) (ConstPat c1 ys) = c1 == c2 && length xs == length xs 

