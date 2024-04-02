module Ast where

import Data.Text (Text)
import Data.Map(Map)
import qualified Data.Map as M
import Data.List(singleton)

type Identifier = Text
type Number = Int

data TypeClass
  = Eq
  | Ord
  deriving (Eq, Show)

type FunctionType = (Type, Type)

data Type
  = TypeVariable Identifier
  | FunctionType FunctionType
  | TypeConstructor TypeConstructor
  deriving (Eq, Show)

countTreeTypes :: Type -> Int
countTreeTypes (TypeVariable _) = 0
countTreeTypes (FunctionType (from, to)) = countTreeTypes from + countTreeTypes to
countTreeTypes (TypeConstructor (Tree _)) = 1
countTreeTypes (TypeConstructor (Product types)) = sum . map countTreeTypes $ types
countTreeTypes (TypeConstructor _) = 0

data TypeConstructor
  = Bool
  | Tree Type
  | Product [Type]
  deriving (Eq, Show)

type TypeConstraint = (TypeClass, Identifier)

data FunctionSignature = FunctionSignature
  {
    sigName :: Identifier,
    sigConstraints :: Maybe [TypeConstraint],
    sigType :: FunctionType,
    sigAnnotation :: Maybe (FunctionAnnotation, Maybe FunctionAnnotation)
  }
  deriving (Eq, Show)

data FunctionDefinition = FunctionDefinition
  {
    funName :: Identifier,
    funSignature :: Maybe FunctionSignature,
    funArgs :: [Identifier],
    funBody :: Expr
  }
  deriving (Eq, Show)

data PatternVar = Identifier Identifier | Wildcard
  deriving (Eq, Show)

data Pattern 
  = TreePattern PatternVar PatternVar PatternVar
  | LeafPattern 
  | TuplePattern PatternVar PatternVar
  | Alias Identifier
  deriving (Eq, Show)

type MatchArm = (Pattern, Expr)

data TreeConstructor 
  = TreeNode Expr Expr Expr
  | TreeLeaf
  deriving (Eq, Show)

type TupleConstructor = (Expr, Expr)

data BooleanConstructor
  = BTrue
  | BFalse
  deriving (Eq, Show)

data DataConstructor
  = TreeConstructor TreeConstructor
  | TupleConstructor TupleConstructor
  | BooleanConstructor BooleanConstructor
  | Number Number
  deriving (Eq, Show)

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
  | Tick (Maybe Rational) Expr
  deriving (Eq, Show)


type Coefficient = Rational

-- TODO: might replaced once the type system is generatlized
type Annotation = Map [Int] Coefficient

zeroAnnotation :: Int -> Annotation
zeroAnnotation size = M.fromList $ zip (map singleton [0..]) (replicate size 0) 
  
type FunctionAnnotation = (Annotation, Annotation)

