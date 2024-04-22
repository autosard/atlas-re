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
import qualified Data.Map as M
import Data.Map(Map)
import Data.Ratio((%))

import Prelude hiding (LT, EQ, GT)

import Text.Megaparsec
import Text.Megaparsec.Char ( letterChar, space1 )
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Error(errorBundlePretty)

import Ast
import Types
import Control.Monad.RWS
import Primitive(Id)

defaultCoinPropability :: Rational
defaultCoinPropability = 1 % 2

newtype ParserContext = ParserContext { ctxModuleName :: String }
data ParserState = ParserState { varIdGen :: Int, typeVarMapping :: Map Id Type }

quantifyTypeVar :: Id -> Parser Type
quantifyTypeVar id = do
  state <- get
  varMap <- gets typeVarMapping
  lastId <- gets varIdGen
  let nextId = lastId + 1
  case M.lookup id varMap of
    Nothing -> do
      let var = TGen lastId
      put state{
        varIdGen = nextId,
        typeVarMapping = M.insert id var varMap
        }
      return var
    Just var -> return var

type Parser = ParsecT Void Text (RWS ParserContext () ParserState)


pModule :: Parser Module
pModule = sc *> manyTill pFunc eof

pFunc :: Parser FunctionDefinition
pFunc = do
  funSignature <- optional pSignature
  funName <- pIdentifier
  args <- manyTill pIdentifier (symbol "=")
  body <- pExpr
  let funBody = Fn args body 
  modName <- asks ctxModuleName
  let funFqn = (modName, T.unpack funName)
  return FunctionDefinition {..}

pSignature :: Parser FunctionSignature
pSignature = do
  sigName <- pIdentifier <?> "function name"
  void pDoubleColon2
  sigConstraints <- optional ((pConstraints <* pDoubleArrow) <?> "type constraint(s)")
  sigType <- pFunctionType
  sigAnnotation <- optional $ symbol "|" *> pSqParens (do
    withCost <- pFunctionAnnotation
    costFree <- optional $ symbol "," *> pCurlyParens pFunctionAnnotation
    return (withCost, costFree))
  return FunctionSignature {..}

pConstraints :: Parser ()
pConstraints = void (try $ pParens (some pConstraint))
  <|> pConstraint

pConstraint :: Parser ()
pConstraint =  pTypeClass <* pIdentifier

pTypeClass :: Parser ()
pTypeClass
  = symbol "Eq"
  <|> symbol "Ord"

pFunctionType :: Parser Scheme
pFunctionType = do
  modify (\s@ParserState{..} -> s{
             varIdGen = 0,
             typeVarMapping = M.empty
             })
  tArgs <- pProdType <|> pType
  pArrow
  tResult <- pType
  len <- gets varIdGen
  return $ Forall len (TAp Arrow [tArgs, tResult])

pProdType :: Parser Type
pProdType = TAp Prod <$> pParens (sepBy1 pType pCross)

pType :: Parser Type
pType = pTypeConst
  <|> (quantifyTypeVar =<< pIdentifier)

pTypeConst :: Parser Type  
pTypeConst
  = (`TAp` []) <$> (Bool <$ symbol "Bool")
  <|> (`TAp` []) <$> (Num <$ symbol "Num")
  <|> TAp <$> (Tree <$ symbol "Tree") <*> (singleton <$> pType)

pFunctionAnnotation :: Parser FunctionAnnotation
pFunctionAnnotation = (,) <$> pAnnotation <* pArrow <*> pAnnotation
  <|> return (Annotation 0 Nothing, Annotation 0 Nothing) 

pAnnotation :: Parser Annotation
pAnnotation = do
  coefs <- pCoefficients
  return $ Annotation (length coefs) (Just (M.fromList coefs))
  

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

pKeywordExpr :: Parser Expr
pKeywordExpr
  = pConstructorExpr
  <|> Lit <$> pNumber
  <|> pParenExpr
  <|> Ite <$ symbol "if" <*> pExpr <* symbol "then" <*> pExpr <* symbol "else" <*> pExpr
  <|> Match <$ symbol "match" <*> pExpr <* symbol "with" <* symbol "|" <*> sepBy1 pMatchArm (symbol "|")
  <|> Let <$ symbol "let" <*> pIdentifier <* symbol "=" <*> pExpr <* symbol "in" <*> pExpr
  <|> Tick <$ symbol "~" <*> optional pRational <*> pExpr
  <|> Coin <$ symbol "coin" <*> ((pRational <?> "coin probability") <|> pure defaultCoinPropability)

pParenExpr :: Parser Expr
pParenExpr = pParens pExpr

pConstructorExpr :: Parser Expr
pConstructorExpr = ConstructorExpr <$> pDataConstructor

pDataConstructor :: Parser DataConstructor
pDataConstructor
  = BooleanConstructor BTrue <$ symbol "true"
  <|> BooleanConstructor BFalse <$ symbol "false"
  <|> TreeConstructor TreeLeaf <$ symbol "leaf"
  <|> TreeConstructor <$> pTreeNode
  <|> TupleConstructor <$> try (pParens pTuple)

pTreeNode = TreeNode <$ symbol "node" <*> pArg <*> pArg <*> pArg

pTuple = (,) <$> pArg <* symbol "," <*> pArg

pMatchArm :: Parser MatchArm
pMatchArm = (,) <$> pPattern <* pArrow <*> pExpr

pPattern :: Parser Pattern
pPattern = pTreePattern
  <|> (LeafPattern <$ symbol "leaf")
  <|> pTuplePattern
  <|> WildcardPattern <$ symbol "_"
  <|> Alias <$> pIdentifier

pTreePattern :: Parser Pattern
pTreePattern = TreePattern <$ symbol "node" <*> pPatternVar <*> pPatternVar <*> pPatternVar

pTuplePattern :: Parser Pattern
pTuplePattern =  pParens (TuplePattern <$> pPatternVar <* symbol "," <*> pPatternVar)

pPatternVar :: Parser PatternVar
pPatternVar = (WildcardVar <$ symbol "_")
  <|> (Id <$> pIdentifier)


pApplication :: Parser Expr
pApplication = do
  identifier <- pIdentifier
  App identifier <$> some pArg

pArg :: Parser Expr
pArg = pParenExpr
  <|> pConstructorExpr
  <|> try (pVar <* notFollowedBy (symbol "=" <|> pDoubleColon2))
  <?> "function argument"

pVar :: Parser Expr
pVar = Var <$> pIdentifier
  
pBTerm :: Parser Expr
pBTerm = pParenExpr <|> pVar

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

pNumber = LitNum <$> lexeme L.decimal

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

run fileName moduleName contents = case fst $ evalRWS rws initEnv initState of
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog
  where initEnv = ParserContext moduleName
        initState = ParserState 0 M.empty
        rws = runParserT pModule fileName contents
