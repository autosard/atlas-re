module Syntax.ResourceExpression.Inequality
  ( ResourceIneq (..)
  , sizeGeOneCs
  ) where

import Syntax (Id, Substitutable (..))
import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM

newtype ResourceIneq = LeZero ResourceExpr
  deriving (Show, Eq, Ord)

instance Substitutable ResourceIneq where
  subst s (LeZero re) = LeZero $ subst s re

sizeGeOneCs :: Id -> ResourceIneq
sizeGeOneCs x = LeZero $ FM.fromList' [(RTSize x, -1), (RTId, 1)]


