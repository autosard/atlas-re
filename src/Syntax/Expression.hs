{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Syntax.Expression
  ( Expr (..)
  , Literal (..)
  , MatchArm (..)
  , calledFunctions
  , printExpr
  , pattern Lit
  , pattern Var
  , pattern Const
  , pattern Ite
  , pattern Match
  , pattern App
  , pattern Let
  , pattern Tick
  , pattern Coin
  , pattern MatchArm
  , armExpr
  ) where

import Prelude hiding (break)
import qualified Data.Text as T
import qualified Data.Set as S
import Data.Set (Set)
import Data.List (intercalate)

import Syntax
  (Id
  , HasVars (..)
  , Parsed
  , Elaborated
  , Typed
  , Positioned)
import Syntax.Annotation
  (XExprAnn
  , TypedExprAnn
  , MapAnnotation (..)
  , HasAnnotation (..)
  , HasType (..))
import Syntax.PrettyPrint (PrettyPrint (..), paren, break)
import Syntax.Pattern
import Syntax.Types.Type (Type)
import Syntax.Types.Subst (Types(..))
import Primitive (unionMap)

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

data Literal
  = LNat Int
  | LRat Rational
  | LString T.Text
  deriving (Eq, Show)

data MatchArm a = MatchArmAnn (XExprAnn a) (Pattern a) (Expr a)

data Expr a
  = LitAnn (XExprAnn a) Literal
  | VarAnn (XExprAnn a) Id
  | ConstAnn (XExprAnn a) Id [Expr a]
  | IteAnn (XExprAnn a) (Expr a) (Expr a) (Expr a)
  | MatchAnn (XExprAnn a) (Expr a) [MatchArm a]
  | AppAnn (XExprAnn a) Id [Expr a]
  | LetAnn (XExprAnn a) Id (Expr a) (Expr a)
  | TickAnn (XExprAnn a) (Maybe Rational) (Expr a)
  | CoinAnn (XExprAnn a) Rational

--------------------------------------------------------------------------------
-- Parsed 
--------------------------------------------------------------------------------

deriving instance Show (Expr Parsed)
deriving instance Eq (Expr Parsed)

deriving instance Show (MatchArm Parsed)
deriving instance Eq (MatchArm Parsed)

--------------------------------------------------------------------------------
-- Elaborated 
--------------------------------------------------------------------------------

deriving instance Show (MatchArm Elaborated)
deriving instance Show (Expr Elaborated)

--------------------------------------------------------------------------------
-- Typed
--------------------------------------------------------------------------------

deriving instance Show (Expr Typed)
deriving instance Eq (Expr Typed)

deriving instance Show (MatchArm Typed)
deriving instance Eq (MatchArm Typed)

instance HasType (Expr Typed) where
  getType = getType . getAnn

instance Types (Expr Typed) where
  apply s = mapAnn (apply s)
  tv e = tv (getType e)

--------------------------------------------------------------------------------
-- Positioned
--------------------------------------------------------------------------------

deriving instance Show (Expr Positioned)
deriving instance Eq (Expr Positioned)

deriving instance Show (MatchArm Positioned)
deriving instance Eq (MatchArm Positioned)

instance HasType (Expr Positioned) where
  getType = getType . getAnn


--------------------------------------------------------------------------------
-- Annotations
--------------------------------------------------------------------------------

instance MapAnnotation Expr a b where
  mapAnn f (LitAnn ann lit) = LitAnn (f ann) lit
  mapAnn f (VarAnn ann id) = VarAnn (f ann) id
  mapAnn f (ConstAnn ann id args) = ConstAnn (f ann) id $ map (mapAnn f) args
  mapAnn f (IteAnn ann e1 e2 e3) = IteAnn (f ann) (mapAnn f e1) (mapAnn f e2) (mapAnn f e3)
  mapAnn f (MatchAnn ann e arms) = MatchAnn (f ann) (mapAnn f e) $ map (mapAnn f) arms
  mapAnn f (AppAnn ann id args) = AppAnn (f ann) id $ map (mapAnn f) args
  mapAnn f (LetAnn ann id e1 e2) = LetAnn (f ann) id (mapAnn f e1) (mapAnn f e2)
  mapAnn f (TickAnn ann c e) = TickAnn (f ann) c (mapAnn f e)
  mapAnn f (CoinAnn ann p) = CoinAnn (f ann) p

instance MapAnnotation MatchArm a b where
  mapAnn f (MatchArmAnn ann p e) = MatchArmAnn (f ann) (mapAnn f p) (mapAnn f e)

instance HasAnnotation MatchArm a where  
  getAnn (MatchArmAnn ann _ _) = ann

--------------------------------------------------------------------------------
-- Pattern Synomyms
--------------------------------------------------------------------------------

-- pattern synomyms to work with epxressions without the overhead of annotations
pattern Lit :: Literal -> Expr a
pattern Lit lit <- LitAnn _ lit
pattern Var :: Id -> Expr a
pattern Var id <- VarAnn _ id
pattern Const :: Id -> [Expr a] -> Expr a
pattern Const id args <- ConstAnn _ id args
pattern Ite :: Expr a -> Expr a -> Expr a -> Expr a
pattern Ite e1 e2 e3 <- IteAnn _ e1 e2 e3
pattern Match :: Expr a -> [MatchArm a] -> Expr a
pattern Match e arms <- MatchAnn _ e arms
pattern App :: Id -> [Expr a] -> Expr a
pattern App id args <- AppAnn _ id args
pattern Let :: Id -> Expr a -> Expr a -> Expr a
pattern Let id e1 e2 <- LetAnn _ id e1 e2
pattern Tick :: Maybe Rational -> Expr a -> Expr a
pattern Tick c e <- TickAnn _ c e
pattern Coin :: Rational -> Expr a
pattern Coin p <- CoinAnn _ p

pattern MatchArm :: Pattern a -> Expr a -> MatchArm a
pattern MatchArm p e <- MatchArmAnn _ p e

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

armExpr :: MatchArm a -> Expr a
armExpr (MatchArmAnn _ _ e) = e

instance HasVars (Expr a) where
  freeVars (Var id) = S.singleton id
  freeVars (Const _ exps) = unionMap freeVars exps
  freeVars (Ite e1 e2 e3) = unionMap freeVars [e1, e2, e3]
  freeVars (Match m arms) = freeVars m `S.union`
    unionMap (freeVars . (\(MatchArm _ e) -> e)) arms
  freeVars (App _ exps) = unionMap freeVars exps
  freeVars (Let id e1 e2) = S.delete id $ freeVars e1 `S.union` freeVars e2
  freeVars (Tick _ e) = freeVars e
  freeVars _ = S.empty

instance HasAnnotation Expr a where
  getAnn (LitAnn ann _) = ann
  getAnn (VarAnn ann _) = ann
  getAnn (ConstAnn ann _ _) = ann
  getAnn (IteAnn ann _ _ _) = ann
  getAnn (MatchAnn ann _ _) = ann
  getAnn (AppAnn ann _ _) = ann
  getAnn (LetAnn ann _ _ _) = ann
  getAnn (TickAnn ann _ _) = ann
  getAnn (CoinAnn ann _) = ann

calledFunctions :: Expr a -> Set Id
calledFunctions (App id exps) = S.insert id $ unionMap calledFunctions exps
calledFunctions (Ite e1 e2 e3) = unionMap calledFunctions [e1, e2, e3]
calledFunctions (Match e1 arms) = calledFunctions e1 `S.union`
  unionMap (calledFunctions . (\(MatchArm _ e) -> e)) arms
calledFunctions (Let _ e1 e2) = unionMap calledFunctions [e1, e2]
calledFunctions (Tick _ e) = calledFunctions e
calledFunctions (Const _ args) = unionMap calledFunctions args
calledFunctions _ = S.empty

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

instance PrettyPrint (Expr a) where
  prettyPrint = printExprHead

printExprHead :: Expr a -> String
printExprHead (Var id) = T.unpack id 
printExprHead (Const id args) = T.unpack id ++ " " ++ unwords (map printExprHead args)
printExprHead (Ite {}) = "ite"
printExprHead (Match (Var id) _) = "match " ++ T.unpack id
printExprHead (App id args) = T.unpack id ++ " " ++ unwords (map printExprHead args)
printExprHead (Let id e1 e2) = "let " ++ T.unpack id ++ " = " ++ printExprHead e1
printExprHead (Tick _ _) = "tick"
printExprHead (Coin _) = "coin"
printExprHead (Lit l) = show l


printExpr :: (XExprAnn a -> String) -> Int -> Expr a -> String
printExpr printAnn _ (LitAnn ann l) = show l ++ printAnn ann
printExpr printAnn _ (VarAnn ann id) = T.unpack id ++ printAnn ann
printExpr printAnn ident (ConstAnn ann "(,)" [x1, x2]) = "(" ++ printExpr printAnn ident x1 ++ ", " ++ printExpr printAnn ident x2 ++ ")" ++ printAnn ann
printExpr printAnn ident (ConstAnn ann id args) = paren $ T.unpack id ++ " " ++ unwords (map (printExpr printAnn ident) args) ++ printAnn ann
printExpr printAnn ident (IteAnn ann e1 e2 e3) = "if " ++ printExpr printAnn ident e1
  ++ printAnn ann 
  ++ break (ident + 1) ++ "then " ++ printExpr printAnn (ident + 1) e2
  ++ break (ident + 1) ++ "else " ++ printExpr printAnn (ident + 1) e3 
printExpr printAnn ident (MatchAnn ann e arms) = "match "
  ++ printExpr printAnn ident e ++ printAnn ann
  ++ break  (ident + 1) ++ printedArms 
  where printedArms = intercalate (break (ident + 1)) . map (printMatchArm printAnn (ident + 1)) $ arms
printExpr printAnn ident (AppAnn ann id args) = paren $ T.unpack id ++ " "
                          ++ (unwords . map (printExpr printAnn ident) $ args) ++ printAnn ann
printExpr printAnn ident (LetAnn ann id e1 e2) = "let " ++ T.unpack id ++ " = " ++ printExpr printAnn ident e1 ++ " in" ++ printAnn ann
                           ++ break (ident + 1) ++ printExpr printAnn (ident + 1) e2
printExpr printAnn ident (TickAnn ann c e) = "~" ++  frac c ++ printExpr printAnn ident e ++ printAnn ann
  where frac = maybe "" prettyPrint
printExpr printAnn ident (CoinAnn ann p) = "coin " ++ prettyPrint p ++ printAnn ann

printMatchArm :: (XExprAnn a -> String) -> Int -> MatchArm a -> String
printMatchArm printAnn ident (MatchArmAnn _ pat e) = "| " ++ printPat pat ++ " -> " ++ printExpr printAnn ident e 


