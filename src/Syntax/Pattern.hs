{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax.Pattern where

import qualified Data.Text as T

import Syntax
  (Id
  , Parsed
  , Elaborated
  , Positioned
  , Typed)
import Syntax.Annotation (XExprAnn, MapAnnotation(..), HasType (..), HasAnnotation (..))

data Pattern a
  = PVar (XExprAnn a) Id
  | PConst (XExprAnn a) Id [Pattern a]
  | PWildcard (XExprAnn a)

instance HasAnnotation Pattern a where
  getAnn (PVar ann _) = ann
  getAnn (PConst ann _ _) = ann
  getAnn (PWildcard ann) = ann

instance HasType (Pattern Positioned) where
  getType (PVar ann _) = getType ann
  getType(PConst ann _ _) = getType ann
  getType (PWildcard ann) = getType ann  
  
--------------------------------------------------------------------------------
-- Parsed 
--------------------------------------------------------------------------------

deriving instance Show (Pattern Parsed)
deriving instance Eq (Pattern Parsed)

--------------------------------------------------------------------------------
-- Elaborated 
--------------------------------------------------------------------------------

deriving instance Show (Pattern Elaborated)

--------------------------------------------------------------------------------
-- Typed
--------------------------------------------------------------------------------

deriving instance Show (Pattern Typed)
deriving instance Eq (Pattern Typed)

instance HasType (Pattern Typed) where
  getType = getType . getAnn 

--------------------------------------------------------------------------------
-- Positioned
--------------------------------------------------------------------------------

deriving instance Show (Pattern Positioned)
deriving instance Eq (Pattern Positioned)

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

printPat :: Pattern a -> String
printPat (PConst _ id ps) = T.unpack id ++ " " ++(unwords . map printPat $ ps)
printPat (PVar _ id) = T.unpack id
printPat (PWildcard _) = "_"

--------------------------------------------------------------------------------
-- Annotations
--------------------------------------------------------------------------------

instance MapAnnotation Pattern a b where
  mapAnn f (PConst ann id vars) = PConst (f ann) id (map (mapAnn f) vars)
  mapAnn f (PVar ann id) = PVar (f ann) id
  mapAnn f (PWildcard ann) = PWildcard (f ann)
  
