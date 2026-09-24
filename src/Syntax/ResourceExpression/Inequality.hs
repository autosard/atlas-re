module Syntax.ResourceExpression.Inequality
  ( ResourceIneq (..)
  , sizeGeOneCs
  , SizeGuardMatrix
  , sizeConstraints
  ) where

import Syntax (Id, Substitutable (..))
import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM
import Data.Map (Map)
import qualified Data.Map as M

newtype ResourceIneq = LeZero RatResourceExpr
  deriving (Show, Eq, Ord)

instance Substitutable ResourceIneq where
  subst s (LeZero re) = LeZero $ subst s re

type SizeGuardMatrix = ([M.Map Id Rational], [Rational])

sizeConstraints :: [ResourceIneq] -> SizeGuardMatrix
sizeConstraints = unzip . map sizeConstraint . filter (all isSize . (\(LeZero re) -> M.keys re))

sizeConstraint :: ResourceIneq -> (Map Id Rational, Rational)
sizeConstraint (LeZero re) =
  let sizeTerms = FM.mapMaybe toSizeVar re
      constTerm = - M.findWithDefault 0 RTId re in
    (sizeTerms, constTerm)
  where toSizeVar (RTSize x) = Just x
        toSizeVar otherTerm  = Nothing


sizeGeOneCs :: Id -> ResourceIneq
sizeGeOneCs x = LeZero $ FM.fromList' [(RTSize x, -1), (RTId, 1)]


