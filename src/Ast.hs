{-# LANGUAGE RecordWildCards   #-}

module Ast where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.List(singleton)
import Data.Set(Set)
import qualified Data.Set as S
import Text.Megaparsec(SourcePos)

import Primitive(Id)
import Types

type Module = [FunctionDefinition]

type Fqn = (String, String)

--type Id = Text
type Number = Int

data FunctionSignature = FunctionSignature
  {
    sigName :: Id,
    sigType :: Scheme,
    sigAnnotation :: Maybe (FunctionAnnotation, Maybe FunctionAnnotation)
  }
  deriving (Eq, Show)


data FunctionDefinition = FunctionDefinition
  {
    funName :: Id,
    funFqn :: Fqn,
    funSignature :: Maybe FunctionSignature,
    funBody :: Expr
  }
  deriving (Eq, Show)

resolveFunId :: String -> Id -> Fqn
resolveFunId currentModule identifier = case suffix of
  [] -> (currentModule, prefix)
  _ -> (prefix, suffix)
  where (prefix, suffix) = break (== '.') $ T.unpack identifier

calledFunctions :: FunctionDefinition -> String -> Set Fqn
calledFunctions FunctionDefinition{..} moduleName =
  S.map (resolveFunId moduleName) $ calledFunctions' funBody

unionMap :: (Ord b) => (a -> Set b) -> [a] -> Set b
unionMap f xs = S.unions $ map f xs

calledFunctions' :: Expr -> Set Id
calledFunctions' (App id exps) = S.insert id $ unionMap calledFunctions' exps
calledFunctions' (Ite e1 e2 e3) = unionMap calledFunctions' [e1, e2, e3]
calledFunctions' (Match e1 arms) = calledFunctions' e1 `S.union` unionMap (calledFunctions' . snd) arms
calledFunctions' (BExpr _ e1 e2) = unionMap calledFunctions' [e1, e2]
calledFunctions' (Let _ e1 e2) = unionMap calledFunctions' [e1, e2]
calledFunctions' (Tick _ e) = calledFunctions' e
calledFunctions' (ConstructorExpr (TreeConstructor (TreeNode e1 e2 e3)))
  = unionMap calledFunctions' [e1, e2, e3]
calledFunctions' (ConstructorExpr (TupleConstructor (e1, e2))) = unionMap calledFunctions' [e1, e2]
calledFunctions' _ = S.empty

data PatternVar = Id Id | WildcardVar
  deriving (Eq, Show)

data Pattern 
  = TreePattern PatternVar PatternVar PatternVar
  | LeafPattern 
  | TuplePattern PatternVar PatternVar
  | Alias Id
  | WildcardPattern
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
  deriving (Eq, Show)

newtype Literal = LitNum Number
  deriving (Eq, Show)

data Op = LT | EQ | GT
  deriving (Eq, Show)

data Expr
  = Var Id
  | Lit Literal
  | ConstructorExpr DataConstructor
  | Ite Expr Expr Expr
  | Match Expr [MatchArm]
  | App Id [Expr]
  | BExpr Op Expr Expr
  | Let Id Expr Expr
  | Tick (Maybe Rational) Expr
  | Coin Rational
  | Fn [Id] Expr
  deriving (Eq, Show)


type Coefficient = Rational

-- TODO: might replaced once the type system is generatlized
data Annotation = Annotation {
  annLen :: Int,
  annCoefs :: Maybe (Map [Int] Coefficient)
  }
  deriving (Eq, Show)

--zeroAnnotation :: Int -> Annotation
--zeroAnnotation size = M.fromList $ zip (map singleton [0..]) (replicate size 0) 
  
type FunctionAnnotation = (Annotation, Annotation)


