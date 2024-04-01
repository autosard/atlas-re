module Ast where

import Data.Text (Text)

type Identifier = Text
type Number = Int

data TypeClass
  = Eq
  | Ord
  deriving (Eq, Show)

data Type
  = TypeVariable Identifier
  | TypeConstructor TypeConstructor
  deriving (Eq, Show)

data TypeConstructor
  = Bool
  | Tree Type
  | Product [Type]
  deriving (Eq, Show)

type TypeConstraint = (TypeClass, Identifier)

data FunctionSignature = FunctionSignature
  {
    sigName :: Identifier,
    sigConstraints :: [TypeConstraint],
    sigFrom :: Type,
    sigTo :: Type
  }
  deriving (Eq, Show)

data FunctionDefinition = FunctionDefinition
  {
    funName :: Identifier,
    funSignature :: Maybe FunctionSignature,
    funBody :: Expr
  }
  deriving (Eq, Show)

type MatchArm = (Pattern, Expr)

data TreeConstructor 
  = TreeNode Identifier Identifier Identifier
  | TreeLeaf
  deriving (Eq, Show)

data BooleanConstructor
  = BTrue
  | BFalse
  deriving (Eq, Show)

data DataConstructor
  = TreeConstructor TreeConstructor
  | BooleanConstructor BooleanConstructor
  | Number Number
  deriving (Eq, Show)

type Pattern = DataConstructor

data Op = LT | EQ | GT
  deriving (Eq, Show)

data Expr
  = Var Identifier
  | ConstructorExpr DataConstructor
  | Ite Expr Expr Expr
  | Match Expr [MatchArm]
  | App Identifier [Expr]
  | BExpr Op Expr Expr
  | Let Identifier Expr Expr
  deriving (Eq, Show)




