{-# LANGUAGE TupleSections #-}

module Parsing.SmtLib where

import CostAnalysis.Constraint

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Void ( Void )
import Control.Monad(void)
import qualified Data.Text as T
import Data.Text(Text)
import qualified Data.Set as S
import Data.Char (isAlphaNum)

import Primitive(Id)
import CostAnalysis.Coeff

type Parser = Parsec Void String

pConstraintString :: Parser Constraint
pConstraintString = space *> pConstraint <* eof

parse :: String -> Constraint
parse contents = case runParser pConstraintString "" contents of
  Left errs -> error $ errorBundlePretty errs
  Right constraint -> constraint

pTerm :: Parser Term
pTerm = (CoeffTerm <$> pCoeff)
  <|> pVar
  <|> ConstTerm <$> pRat
  <|> try (Sum <$> pOp "+")
  <|> try (Diff <$> pOp "-")
  <|> try (Prod <$> pOp "*")
  

pVar :: Parser Term
pVar = do
  symbol "k_"
  VarTerm <$> pInt

pCoeff :: Parser Coeff
pCoeff = pBars (do
  symbol "q"
  id <- pInt
  symbol "_"
  idx <- pCoeffIdx
  (label, comment) <- pCurly pLabelComment
  return $ Coeff id label comment idx)

pOp :: String -> Parser [Term]
pOp op = pParens (do
                     symbol op
                     many pTerm)


pConstraint :: Parser Constraint
pConstraint = pParens (try (uncurry Eq <$> pBinOp "=")
                       <|> pZero
                       <|> uncurry Le <$> pBinOp "<="
                       <|> uncurry Ge <$> pBinOp ">="
                       <|> uncurry Impl <$> pBinOp2 "=>"
                       <|> pNot)

pBinOp :: String -> Parser (Term, Term)
pBinOp op = do
  symbol op
  (,) <$> pTerm <*> pTerm

pBinOp2 :: String -> Parser (Constraint, Constraint)
pBinOp2 op = do
  symbol op
  (,) <$> pConstraint <*> pConstraint

pNot :: Parser Constraint
pNot = do
  symbol "not"
  Not <$> pConstraint

pZero = do
  symbol "="
  Zero <$> pTerm <* symbol "0.0"
  
pLabelComment :: Parser (Text, Text)
pLabelComment = do
  label <- T.pack <$> stringLiteral
  symbol ","
  comment <- T.pack <$> stringLiteral
  return (label, comment)
  
  
pCoeffIdx :: Parser CoeffIdx
pCoeffIdx = pParens (
  try (do
      args <- sepBy pFactor (symbol ",")  
      return $ Mixed (S.fromList args))
    <|> (Pure <$> pIdentifier))
           

pFactor :: Parser Factor
pFactor = (Const <$> pInt) <|> pArg

pPure = pIdentifier
  
pArg :: Parser Factor  
pArg = Arg <$> pIdentifier <* symbol "^" <*> pInt

pAnomId :: Parser String
pAnomId = lexeme ((++) <$> string "?:" <*> (show <$> pInt))
  

pIdentifier :: Parser Id
pIdentifier = do
  id <- lexeme ((:) <$> letterChar <*> takeWhileP Nothing (\x -> isAlphaNum x || (x == '?') || (x == ':')
                                                            || (x == '_') || (x == '.')))
        <|> pAnomId <?> "identifier"
  return $ T.pack id

  
pParens = between (symbol "(") (symbol ")")

pBars = between (symbol "|") (symbol "|")
pCurly = between (symbol "{") (symbol "}")

symbol :: String -> Parser ()
symbol = void . L.symbol space

pInt :: Parser Int
pInt = lexeme L.decimal

pRat :: Parser Rational
pRat = realToFrac <$> lexeme L.float

stringLiteral :: Parser String
stringLiteral = char '\"' *> manyTill L.charLiteral (char '\"')

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space
