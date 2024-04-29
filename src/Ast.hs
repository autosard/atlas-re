{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-} 


module Ast where

import Data.Text (Text)
import Data.Map(Map)
import Text.Megaparsec(SourcePos)

import Primitive(Id)
import Typing.Type (Type)
import Typing.Scheme (Scheme)


type Fqn = (Text, Text)

--type Id = Text
type Number = Int



-- data TreeConstructor a
--   = TreeNode (Expr a) (Expr a) (Expr a)
--   | TreeLeaf
-- --   deriving (Eq, Show)

-- type TupleConstructor a = (Expr a, Expr a)

-- data BooleanConstructor
--   = BTrue
--   | BFalse
--   deriving (Eq, Show)

-- data DataConst a
--   = TreeConstructor (TreeConstructor a)
--   | TupleConstructor (TupleConstructor a)
--   | BooleanConstructor BooleanConstructor
--  deriving (Eq, Show)
type Module a = [FunDef a]

data FunDef a = FunDef (XFunAnn a) Id [Id] (Expr a)

newtype Literal = LitNum Number
  deriving (Eq, Show)

data Op = LT | EQ | GT
  deriving (Eq, Show)

data Syntax a
   = SynExpr (Expr a)
   | SynArm (MatchArm a)
   | SynPat (Pattern a)

data MatchArm a = MatchArmAnn (XExprAnn a) (Pattern a) (Expr a)

data PatternVar = Id Id | WildcardVar
  deriving (Eq, Show)

data Pattern a
  = ConstPat (XExprAnn a) Id [PatternVar]
  | Alias (XExprAnn a) Id
  | WildcardPat (XExprAnn a) 

-- We use extensible AST types to model the different stages (parsed, typed, etc.) (see https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf)

data Expr a
  = VarAnn (XExprAnn a) Id
  | LitAnn (XExprAnn a) Literal
  | ConstAnn (XExprAnn a) Id [Expr a]
  | IteAnn (XExprAnn a) (Expr a) (Expr a) (Expr a)
  | MatchAnn (XExprAnn a) (Expr a) [MatchArm a]
  | AppAnn (XExprAnn a) Id [Expr a]
  | BExprAnn (XExprAnn a) Op (Expr a) (Expr a)
  | LetAnn (XExprAnn a) Id (Expr a) (Expr a)
  | TickAnn (XExprAnn a) (Maybe Rational) (Expr a)
  | CoinAnn (XExprAnn a) Rational

type family XExprAnn a
type family XFunAnn a

-- pattern synomyms for constants
pattern ConstTreeNode :: Expr a -> Expr a -> Expr a -> Expr a
pattern ConstTreeNode l v r <- ConstAnn _ "node" [l, v, r]
pattern ConstTreeLeaf :: Expr a
pattern ConstTreeLeaf <- ConstAnn _ "leaf" []
pattern ConstTuple :: Expr a -> Expr a -> Expr a
pattern ConstTuple x y <- ConstAnn _ "(,)" [x, y]
pattern ConstTrue :: Expr a
pattern ConstTrue <- ConstAnn _ "true" []
pattern ConstFalse :: Expr a
pattern ConstFalse <- ConstAnn _ "false" []

-- pattern synomyms for constructor patterns
pattern PatTreeNode :: PatternVar -> PatternVar -> PatternVar -> Pattern a
pattern PatTreeNode l v r <- ConstPat _ "node" [l, v, r]
pattern PatTreeLeaf :: Pattern a
pattern PatTreeLeaf <- ConstPat _ "leaf" []
pattern PatTuple :: PatternVar -> PatternVar -> Pattern a
pattern PatTuple x y <- ConstPat _ "(,)" [x, y]

-- pattern synomyms to work with epxressions without the overhead of annotations
pattern Var :: Id -> Expr a
pattern Var id <- VarAnn _ id
pattern Lit :: Literal -> Expr a
pattern Lit l <- LitAnn _ l
pattern Const :: Id -> [Expr a] -> Expr a
pattern Const id args <- ConstAnn _ id args
pattern Ite :: Expr a -> Expr a -> Expr a -> Expr a
pattern Ite e1 e2 e3 <- IteAnn _ e1 e2 e3
pattern Match :: Expr a -> [MatchArm a] -> Expr a
pattern Match e arms <- MatchAnn _ e arms
pattern App :: Id -> [Expr a] -> Expr a
pattern App id args <- AppAnn _ id args
pattern BExpr :: Op -> Expr a -> Expr a -> Expr a
pattern BExpr op e1 e2 <- BExprAnn _ op e1 e2
pattern Let :: Id -> Expr a -> Expr a -> Expr a
pattern Let id e1 e2 <- LetAnn _ id e1 e2
pattern Tick :: Maybe Rational -> Expr a -> Expr a
pattern Tick c e <- TickAnn _ c e
pattern Coin :: Rational -> Expr a
pattern Coin p <- CoinAnn _ p

pattern PatWildcard :: Pattern a
pattern PatWildcard <- WildcardPat _
pattern PatAlias :: Id -> Pattern a
pattern PatAlias id <- Alias _ id

pattern MatchArm :: Pattern a -> Expr a -> MatchArm a
pattern MatchArm p e <- MatchArmAnn _ p e

pattern Fn :: Id -> [Id] -> Expr a -> FunDef a
pattern Fn id args e <- FunDef _ id args e

-- parsed
type ParsedSyntax = Syntax Parsed
type ParsedModule = Module Parsed
type ParsedFunDef = FunDef Parsed
type ParsedExpr = Expr Parsed
type ParsedMatchArm = MatchArm Parsed
type ParsedPattern = Pattern Parsed

deriving instance Show ParsedPattern
deriving instance Show ParsedMatchArm
deriving instance Show ParsedExpr


data ParsedFunAnn = ParsedFunAnn {
  pfLoc :: SourcePos,
  pfFqn :: Fqn,
  pfType :: Maybe Scheme,
  pfResourceAnn :: Maybe FullResourceAnn}

data Parsed
type instance XExprAnn Parsed = SourcePos
type instance XFunAnn Parsed = ParsedFunAnn

pattern FnParsed :: ParsedFunAnn -> Id -> [Id] -> ParsedExpr -> ParsedFunDef
pattern FnParsed ann id args body = FunDef ann id args body

funAnn :: FunDef a -> XFunAnn a
funAnn (FunDef ann _ _ _) = ann

synAnn :: Syntax a -> XExprAnn a
synAnn (SynExpr (VarAnn ann _)) = ann
synAnn (SynExpr (ConstAnn ann _ _)) = ann
synAnn (SynExpr (LitAnn ann _)) = ann
synAnn (SynExpr (IteAnn ann _ _ _)) = ann
synAnn (SynExpr (MatchAnn ann _ _)) = ann
synAnn (SynExpr (AppAnn ann _ _)) = ann
synAnn (SynExpr (BExprAnn ann _ _ _)) = ann
synAnn (SynExpr (LetAnn ann _ _ _ )) = ann
synAnn (SynExpr (TickAnn ann _ _)) = ann
synAnn (SynExpr (CoinAnn ann _ )) = ann
synAnn (SynArm (MatchArmAnn ann _ _)) = ann

-- typed
type TypedExpr = Expr Typed

data TypedExprAnn = TypedExprAnn {
  teLoc :: SourcePos,
  teType :: Type}
  
data Typed
type instance XExprAnn Typed = TypedExprAnn
type instance XFunAnn Typed = ParsedFunAnn

type Coefficient = Rational

-- TODO: might replaced once the type system is generatlized
type FullResourceAnn = (FunResourceAnn, Maybe FunResourceAnn)

data ResourceAnn = ResourceAnn {
  annLen :: Int,
  annCoefs :: Maybe (Map [Int] Coefficient)
  }
  deriving (Eq, Show)

--zeroAnnotation :: Int -> Annotation
--zeroAnnotation size = M.fromList $ zip (map singleton [0..]) (replicate size 0) 
  
type FunResourceAnn = (ResourceAnn, ResourceAnn)
