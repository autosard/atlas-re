module Syntax.ResourceExpression where

import Primitive(Id)

data SizeTerm
  = SVar Id
  | SConst Int
  | SScalar Int SizeTerm
  deriving (Eq, Ord, Show)

data ResourceTerm
  = RTSize SizeTerm
  | Binoms [(SizeTerm, Int)]
  | Log [SizeTerm]
  | Phi Id
  | RTId 
  -- special form for specifing potential functions
  -- this is normalized aways in templates
  | RTScale Rational ResourceTerm
  deriving (Eq, Ord, Show)

