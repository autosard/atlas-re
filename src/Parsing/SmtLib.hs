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
import Data.Maybe(isJust)
import Data.Ratio((%))
import Data.Functor(($>))

import Primitive(Id)
import CostAnalysis.Coeff

type Parser = Parsec Void String

pConstraint :: Parser Constraint
pConstraint = space *> pAst <* eof

parse :: String -> Constraint
parse contents = case runParser pAst "" contents of
  Left errs -> error $ errorBundlePretty errs
  Right constraint -> constraint

pAst :: Parser Constraint
pAst = pParens (pLe <|> pEq)

pLe :: Parser Constraint
pLe = do
  symbol "<="
  try (do
          var <- pVar
          sum <- pSum
          return $ GeSum sum var)

pEq :: Parser Constraint
pEq = do
  symbol "=" 
  try (Eq <$> pVar <*> pVar)
    <|> try pZero
    <|> try (EqSum <$> pVar <*> pParens pSum)
    <|> try (do
                v1 <- pVar
                (v2, c) <- pParens pAddConst
                return $ EqPlusConst v1 v2 c)
    <|> try (do
                v1 <- pVar
                (v2, c) <- pParens pSubConst
                return $ EqMinusConst v1 v2 c)
    <|> try (do
                v1 <- pVar
                (v2, v3, k) <- pParens (do
                  symbol "+"
                  v2 <- pVar
                  (v3, k) <- pParens ((,) <$> (symbol "*" *> pVar) <*> pVar)
                  return (v2, v3, k))
                return $ EqPlusMulti v1 v2 v3 k
            )
    <|> try (do
                v1 <- pVar
                (v2, v3) <- pParens ((,) <$> (symbol "-" *> pVar) <*> pVar)
                return $ EqMinusVar v1 v2 v3)
    

pZero :: Parser Constraint  
pZero = do
  v1 <- pVar
  symbol "0.0"
  return $ Zero v1  

pMulConst :: Parser (Var, Rational)          
pMulConst = (,) <$> (symbol "*" *> pVar) <*> pRat

pAddConst :: Parser (Var, Rational)          
pAddConst = (,) <$> (symbol "+" *> pVar) <*> pRat

pSubConst :: Parser (Var, Rational)          
pSubConst = (,) <$> (symbol "-" *> pVar) <*> pRat            
          
pSum :: Parser [Var]
pSum = do
  symbol "+"
  many pVar

pVar :: Parser Var
pVar = (do
  symbol "k"
  pos <- isJust <$> optional (symbol "+")
  symbol "_"
  Var pos <$> pInt) <|> (AnnCoeff <$> pCoeff) <?> "var"

pCoeff :: Parser Coeff
pCoeff = pBars (do
  symbol "q"
  id <- pInt
  symbol "_"
  idx <- pCoeffIdx
  (label, comment) <- pCurly pLabelComment
  return $ Coeff id label comment idx)
  
pLabelComment :: Parser (Text, Text)
pLabelComment = do
  label <- T.pack <$> stringLiteral
  symbol ","
  comment <- T.pack <$> stringLiteral
  return (label, comment)
  
  
pCoeffIdx :: Parser CoeffIdx
pCoeffIdx = pParens (
  try (do
      args <- sepBy1 pFactor (symbol ",")  
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
