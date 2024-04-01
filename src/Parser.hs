{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Parser where

import Control.Monad 
import Control.Applicative hiding (many, some)
import Data.List(singleton)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Control.Monad.Combinators.Expr
import Data.Char (isAlphaNum, isLetter)

import Prelude hiding (LT, EQ, GT)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Error(errorBundlePretty)

import Ast

import Text.Megaparsec.Debug(dbg)

type Parser = Parsec Void Text 

sc :: Parser ()
sc = L.space
  space1                        
  (L.skipLineComment "(*)")       
  (L.skipBlockComment "(*" "*)")
  
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser ()
symbol = void . L.symbol sc

--

pIdentifier :: Parser Text
pIdentifier = lexeme
  (T.cons <$> letterChar <*> takeWhileP Nothing isAlphaNum <?> "identifier")


pBExpr :: Parser Expr
pBExpr = makeExprParser pExpr boolOperatorTable 

binaryBool :: Text -> Op -> Operator Parser Expr
binaryBool name op = InfixN (BExpr op <$ symbol name)

boolOperatorTable :: [[Operator Parser Expr]]
boolOperatorTable =
  [
    [
      binaryBool "<" LT,
      binaryBool "=" EQ,
      binaryBool ">" GT
    ]
  ]

pNumber = Number <$> lexeme L.decimal

pTreeNode = TreeNode <$ symbol "node" <*> pIdentifier <*> pIdentifier <*> pIdentifier
  
pDataConstructor :: Parser DataConstructor
pDataConstructor
  = pNumber
  <|> BooleanConstructor BTrue <$ symbol "true"
  <|> BooleanConstructor BFalse <$ symbol "false"
  <|> TreeConstructor TreeLeaf <$ symbol "leaf"
  <|> TreeConstructor <$> pTreeNode

pMatchArm :: Parser MatchArm
pMatchArm = (,) <$> pDataConstructor <* pArrow <*> pExpr

pParens = between (symbol "(") (symbol ")")
pArrow = symbol "->" <|> symbol "→"
pDoubleArrow = symbol "=>" <|> symbol "⇒"
pDoubleColon2 = symbol "::" <|> symbol "∷"
pCross = symbol "⨯" <|> symbol "*"


pProgram :: Parser [FunctionDefinition]
pProgram = sc *> manyTill pFunc eof

pTypeClass :: Parser TypeClass
pTypeClass
  = (Eq <$ symbol "Eq")
  <|> (Ord <$ symbol "Ord")

pConstraint :: Parser TypeConstraint
pConstraint = (,) <$> pTypeClass <*> pIdentifier

pTypeConstructor :: Parser TypeConstructor
pTypeConstructor
  = Bool <$ symbol "Bool"
  <|> Tree <$ symbol "Tree" <*> pType
  <|> Product <$> pParens (sepBy1 pType pCross)

pType :: Parser Type 
pType
  = TypeConstructor <$> pTypeConstructor 
  <|> TypeVariable <$> pIdentifier
  <?> "type"

pSignature :: Parser FunctionSignature
pSignature = do
  sigName <- pIdentifier
  void pDoubleColon2
  sigConstraints <- pParens (some pConstraint)
    <|> (singleton <$> pConstraint)
    <|> pure []
  void pDoubleArrow
  sigFrom <- pType
  void pArrow
  sigTo <- pType
  return FunctionSignature {..}
  

pFunc :: Parser FunctionDefinition
pFunc = do
  funSignature <- optional pSignature
  funName <- dbg "function name" pIdentifier
  funBody <- pExpr
  return FunctionDefinition {..}

  
pExpr :: Parser Expr 
pExpr 
  = ConstructorExpr <$> pDataConstructor
  <|> Ite <$ symbol "if" <*> pExpr <* symbol "then" <*> pExpr <* symbol "else" <*> pExpr
  <|> Match <$ symbol "match" <*> pExpr <* symbol "with" <*> sepBy1 pMatchArm (symbol "|")
  <|> Let <$ symbol "let" <*> pIdentifier <* symbol "=" <*> pExpr <* symbol "in" <*> pExpr
  <|> pBExpr -- boolean expression
  <|> Var <$> pIdentifier
  <?> "expression"

run fileName contents = case parse pProgram fileName contents of
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog
