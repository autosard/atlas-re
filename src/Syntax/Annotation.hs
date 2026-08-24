{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Syntax.Annotation
  ( XExprAnn
  , MapAnnotation (..)
  , HasAnnotation (..)
  , HasType (..)
  , TypedExprAnn (..)
  , PositionedExprAnn (..)
  , ExprSrc (..)
  , ExprCtx (..)
  , extendWithType
  , extendWithCtx
  ) where

import Syntax (Parsed, Typed, Elaborated, Positioned)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)
import Text.Megaparsec (SourcePos)

import Syntax.Types.Type
import Syntax.Types.Subst (Types(..))

class HasType a where
  getType :: a -> Type

--------------------------------------------------------------------------------
-- Annotations
--------------------------------------------------------------------------------

type family XExprAnn a  

class HasAnnotation a b where
  getAnn :: a b -> XExprAnn b
  
class MapAnnotation a b c where
  mapAnn :: (XExprAnn b -> XExprAnn c) -> a b -> a c

type instance XExprAnn Parsed = SourcePos
type instance XExprAnn Elaborated = SourcePos

data ExprSrc = Loc SourcePos | DerivedFrom SourcePos
  deriving (Eq, Show)

data TypedExprAnn = TypedExprAnn {
  teSrc :: ExprSrc,
  teType :: Type}
  deriving (Eq, Show)

type instance XExprAnn Typed = TypedExprAnn

instance Types TypedExprAnn where
  apply s ann = ann{teType = apply s (teType ann) }
  tv ann = tv (teType ann)

instance HasType TypedExprAnn where
  getType = teType

data ExprCtx = PseudoLeaf
  | RecCall 
  | BindsAppOrTick
  | BindsAppOrTickRec
  | FirstAfterApp
  | OutermostLet
  | FirstAfterMatch
  | IteCoin
  deriving (Eq, Ord, Show)

data PositionedExprAnn = PositionedExprAnn {
  peSrc :: ExprSrc,
  peType :: Type,
  peCtx :: Set ExprCtx}
  deriving (Eq, Show)

type instance XExprAnn Positioned = PositionedExprAnn

instance HasType PositionedExprAnn where
  getType = peType 

extendWithType :: Type -> XExprAnn Parsed -> XExprAnn Typed
extendWithType t pos = TypedExprAnn (Loc pos) t

extendWithCtx :: Set ExprCtx -> XExprAnn Typed -> XExprAnn Positioned
extendWithCtx ctx (TypedExprAnn {..}) = PositionedExprAnn teSrc teType ctx
