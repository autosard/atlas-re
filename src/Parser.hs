{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Parser(run) where

import Control.Monad 
import Control.Applicative hiding (many, some)

import Data.List(singleton)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void ( Void )
import Control.Monad.Combinators.Expr
import Data.Char (isAlphaNum, isLetter)
import qualified Data.Map as Map
import Data.Ratio((%))

import Prelude hiding (LT, EQ, GT)

import Text.Megaparsec
import Text.Megaparsec.Char ( letterChar, space1 )
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Error(errorBundlePretty)

import Ast
import Control.Monad.Reader (Reader, runReader, asks, MonadTrans (lift))

defaultCoinPropability :: Rational
defaultCoinPropability = 1 % 2

newtype ParserContext = ParserContext { ctxModuleName :: String }
  

type Parser = ParsecT Void Text (Reader ParserContext)


pModule :: Parser Module
pModule = sc *> manyTill pFunc eof

pFunc :: Parser FunctionDefinition
pFunc = do
  funSignature <- optional pSignature
  name <- T.unpack <$> pIdentifier
  funArgs <- manyTill pIdentifier (symbol "=")
  funBody <- pExpr
  modName <- asks ctxModuleName
  let funFqn = (modName, name)
  return FunctionDefinition {..}

pSignature :: Parser FunctionSignature
pSignature = do
  sigName <- pIdentifier <?> "function name"
  void pDoubleColon2
  sigConstraints <- optional ((pConstraints <* pDoubleArrow) <?> "type constraint(s)")
  (from, to) <- (,) <$> pType <* pArrow <*> pType
  let fromSize = countTreeTypes from
  let toSize = countTreeTypes to
  let sigType = (from, to)
  let pFunctionAnnotation' = pFunctionAnnotation fromSize toSize
  sigAnnotation <- optional $ symbol "|" *> pSqParens (do
    withCost <- pFunctionAnnotation'
    costFree <- optional $ symbol "," *> pCurlyParens pFunctionAnnotation'
    return (withCost, costFree))
  return FunctionSignature {..}

pConstraints :: Parser [TypeConstraint]
pConstraints = try $ pParens (some pConstraint)
  <|> (singleton <$> pConstraint)
  <|> pure []

pConstraint :: Parser TypeConstraint
pConstraint = (,) <$> pTypeClass <*> pIdentifier

pTypeClass :: Parser TypeClass
pTypeClass
  = (Eq <$ symbol "Eq")
  <|> (Ord <$ symbol "Ord")

pType :: Parser Type 
pType
  = TypeConstructor <$> pTypeConstructor 
  <|> TypeVariable <$> pIdentifier
  <?> "type"

pTypeConstructor :: Parser TypeConstructor
pTypeConstructor
  = Bool <$ symbol "Bool"
  <|> Tree <$ symbol "Tree" <*> pType
  <|> Product <$> pParens (sepBy1 pType pCross)

pFunctionAnnotation :: Int -> Int -> Parser FunctionAnnotation
pFunctionAnnotation fromSize toSize = (,) <$> pAnnotation <* pArrow <*> pAnnotation
  <|> pure (zeroAnnotation fromSize, zeroAnnotation toSize)

pAnnotation :: Parser Annotation
pAnnotation = Map.fromList <$> pCoefficients 

pCoefficients :: Parser [([Int], Coefficient)]
pCoefficients = pSqParens $ sepBy pCoefficient (symbol ",")

pCoefficient :: Parser ([Int], Coefficient)
pCoefficient = do
  index <- (singleton <$> pInt) <|> pNumberList
  void pMapsTo
  coefficient <- try pRational <|> toRational <$> pInt
  return (index, coefficient)

pExpr :: Parser Expr 
pExpr = pKeywordExpr
  <|> try pApplication
  <|> try pBExpr 
  <?> "expression"

pExprShortest :: Parser Expr
pExprShortest = pKeywordExpr
  <|> try pBExpr 
  <|> try pApplication

pKeywordExpr :: Parser Expr
pKeywordExpr
  = ConstructorExpr <$> pDataConstructor
  <|> pParens pExpr
  <|> Ite <$ symbol "if" <*> pExpr <* symbol "then" <*> pExpr <* symbol "else" <*> pExpr
  <|> Match <$ symbol "match" <*> pExpr <* symbol "with" <* symbol "|" <*> sepBy1 pMatchArm (symbol "|")
  <|> Let <$ symbol "let" <*> pIdentifier <* symbol "=" <*> pExpr <* symbol "in" <*> pExpr
  <|> Tick <$ symbol "~" <*> optional pRational <*> pExpr
  <|> Coin <$ symbol "coin" <*> ((pRational <?> "coin probability") <|> pure defaultCoinPropability)


pDataConstructor :: Parser DataConstructor
pDataConstructor
  = pNumber
  <|> BooleanConstructor BTrue <$ symbol "true"
  <|> BooleanConstructor BFalse <$ symbol "false"
  <|> TreeConstructor TreeLeaf <$ symbol "leaf"
  <|> TreeConstructor <$> pTreeNode
  <|> TupleConstructor <$> try (pParens pTuple)

pTreeNode = TreeNode <$ symbol "node" <*> pExprShortest <*> pExprShortest <*> pExprShortest

pTuple = (,) <$> pExprShortest <* symbol "," <*> pExprShortest

pMatchArm :: Parser MatchArm
pMatchArm = (,) <$> pPattern <* pArrow <*> pExpr

pPattern :: Parser Pattern
pPattern = pTreePattern
  <|> (LeafPattern <$ symbol "leaf")
  <|> pTuplePattern
  <|> Alias <$> pIdentifier

pTreePattern :: Parser Pattern
pTreePattern = TreePattern <$ symbol "node" <*> pPatternVar <*> pPatternVar <*> pPatternVar

pTuplePattern :: Parser Pattern
pTuplePattern =  pParens (TuplePattern <$> pPatternVar <* symbol "," <*> pPatternVar)

pPatternVar :: Parser PatternVar
pPatternVar = (Wildcard <$ symbol "_")
  <|> (Identifier <$> pIdentifier)


resolveFunId :: String -> Identifier -> Fqn
resolveFunId currentModule identifier = case suffix of
  [] -> (currentModule, prefix)
  _ -> (prefix, suffix)
  where (prefix, suffix) = break (== '.') $ T.unpack identifier

pApplication :: Parser Expr
pApplication = do
  identifier <- pIdentifier
  currentModule <- asks ctxModuleName
  let fqn = resolveFunId currentModule identifier
  App fqn <$> some pExprShortest

pBTerm :: Parser Expr
pBTerm = pParens pExpr <|> Var <$> pIdentifier

pBExpr :: Parser Expr
pBExpr = makeExprParser pBTerm boolOperatorTable 

binaryBool :: Parser () -> Op -> Operator Parser Expr
binaryBool parser op = InfixL (BExpr op <$ parser)

boolOperatorTable :: [[Operator Parser Expr]]
boolOperatorTable =
  [
    [
      binaryBool (symbol "<") LT,
      binaryBool (symbol "==" <|> symbol "⩵") EQ,
      binaryBool (symbol ">") GT
    ]
  ]

keywords = [ "if", "then", "else", "match", "with", "let", "in"]

pIdentifier :: Parser Text
pIdentifier = do
  ident <- lexeme (T.cons <$> letterChar <*>
                   takeWhileP Nothing (\x -> isAlphaNum x || (x == '_') || (x == '.')) <?> "identifier")
  if ident `elem` keywords
    then fail $ "Use of reserved keyword " ++ T.unpack ident
    else return ident

pNumberList :: Parser [Int]
pNumberList = pParens $ some pInt 

pInt :: Parser Int
pInt = lexeme L.decimal

pNumber = Number <$> lexeme L.decimal

pInteger :: Parser Integer
pInteger = lexeme L.decimal

pRational :: Parser Rational
pRational = (%) <$> pInteger <* symbol "/" <*> pInteger

pParens = between (symbol "(") (symbol ")")
pSqParens = between (symbol "[") (symbol "]")
pCurlyParens = between (symbol "{") (symbol "}")
pArrow = symbol "->" <|> symbol "→"
pDoubleArrow = symbol "=>" <|> symbol "⇒"
pDoubleColon2 = symbol "::" <|> symbol "∷"
pCross = symbol "⨯" <|> symbol "*"
pMapsTo = symbol "↦" <|> symbol "|->"

symbol :: Text -> Parser ()
symbol = void . L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

sc :: Parser ()
sc = L.space
  space1                        
  (L.skipLineComment "(*)")       
  (L.skipBlockComment "(*" "*)")

run fileName moduleName contents = case runReader reader (ParserContext moduleName) of
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog
  where reader = runParserT pModule fileName contents
