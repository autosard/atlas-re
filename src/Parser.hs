{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections #-}

module Parser(run, initialPos) where

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

newtype ParserContext = ParserContext { ctxModuleName :: Text }
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


pModule :: Parser ParsedModule
pModule = sc *> manyTill pFunc eof

pFunc :: Parser ParsedFunDef
pFunc = do
  pos <- getSourcePos
  sig <- optional (try pSignature)
  funName <- pIdentifier
  (_type, resourceAnn) <- case sig of
    Just (name, _type, resouceAnn) -> do
      when (funName /= name ) (fail $ "Signature for function '" ++ T.unpack name ++ "' must be followod by defining equation.")
      return (Just _type, resouceAnn)
    Nothing -> return (Nothing, Nothing)
  modName <- asks ctxModuleName
  let funFqn = (modName, funName)
  args <- manyTill pIdentifier (symbol "=")
  FunDef (ParsedFunAnn pos funFqn _type resourceAnn) funName args <$> pExpr

pSignature :: Parser (Id, Scheme, Maybe FullResourceAnn)
pSignature = do
  name <- pIdentifier <?> "function name"
  void pDoubleColon2
  constraints <- optional ((pConstraints <* pDoubleArrow) <?> "type constraint(s)")
  _type <- pFunctionType
  resourceAnn <- optional $ symbol "|" *> pSqParens (do
    withCost <- pFunResourceAnn
    costFree <- optional $ symbol "," *> pCurlyParens pFunResourceAnn
    return (withCost, costFree))
  return (name, _type, resourceAnn)

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
  tArgs <- pArgsType
  pArrow
  tResult <- pType
  len <- gets varIdGen
  return $ Forall len (TAp Arrow [tArgs, tResult])

pArgsType :: Parser Type
pArgsType = do
  args <- pParens (sepBy1 pType pCross)
    <|> (singleton <$> pType)
  return $ TAp Prod args

pType :: Parser Type
pType = pTypeConst
  <|> (quantifyTypeVar =<< pIdentifier)

pTypeConst :: Parser Type  
pTypeConst
  = (`TAp` []) <$> (Bool <$ symbol "Bool")
  <|> (`TAp` []) <$> (Num <$ symbol "Num")
  <|> TAp <$> (Tree <$ symbol "Tree") <*> (singleton <$> pType)

pFunResourceAnn :: Parser FunResourceAnn
pFunResourceAnn = (,) <$> pResourceAnn <* pArrow <*> pResourceAnn
  <|> return (ResourceAnn 0 Nothing, ResourceAnn 0 Nothing) 

pResourceAnn :: Parser ResourceAnn
pResourceAnn = do
  coefs <- pCoefficients
  return $ ResourceAnn (length coefs) (Just (M.fromList coefs))
  

pCoefficients :: Parser [([Int], Coefficient)]
pCoefficients = pSqParens $ sepBy pCoefficient (symbol ",")

pCoefficient :: Parser ([Int], Coefficient)
pCoefficient = do
  index <- (singleton <$> pInt) <|> pNumberList
  void pMapsTo
  coefficient <- try pRational <|> toRational <$> pInt
  return (index, coefficient)

pExpr :: Parser ParsedExpr
pExpr = pKeywordExpr
  <|> try pApplication
  <|> try pBExpr 
  <?> "expression"

pKeywordExpr :: Parser ParsedExpr
pKeywordExpr
  = pConst
  <|> LitAnn <$> getSourcePos <*> pNumber
  <|> pParenExpr
  <|> IteAnn <$> getSourcePos <* symbol "if" <*> pExpr <* symbol "then" <*> pExpr <* symbol "else" <*> pExpr
  <|> MatchAnn <$> getSourcePos <* symbol "match" <*> pExpr <* symbol "with" <* symbol "|" <*> sepBy1 pMatchArm (symbol "|")
  <|> LetAnn <$> getSourcePos <* symbol "let" <*> pIdentifier <* symbol "=" <*> pExpr <* symbol "in" <*> pExpr
  <|> TickAnn <$> getSourcePos <* symbol "~" <*> optional pRational <*> pExpr
  <|> CoinAnn <$> getSourcePos <* symbol "coin" <*> ((pRational <?> "coin probability") <|> pure defaultCoinPropability)

pParenExpr :: Parser ParsedExpr
pParenExpr = pParens pExpr

pConst :: Parser ParsedExpr
pConst = do
  pos <- getSourcePos
  (name, args) <- (,) <$> symbol' "true" <*> pure []
    <|> (,) <$> symbol' "false" <*> pure []
    <|> (,) <$> symbol' "node" <*> count 3 pArg
    <|> (,) <$> symbol' "leaf" <*> pure []
    <|> ("(,)",) <$> try (pParens ((\x y -> [x, y]) <$> pArg <* symbol "," <*> pArg))
  return $ ConstAnn pos name args
  

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


pApplication :: Parser ParsedExpr
pApplication = AppAnn <$> getSourcePos <*> pIdentifier <*> some pArg

pArg :: Parser ParsedExpr
pArg = pParenExpr
  <|> pConst
  <|> try (pVar <* notFollowedBy (symbol "=" <|> pDoubleColon2))
  <?> "function argument"

pVar :: Parser ParsedExpr
pVar = VarAnn <$> getSourcePos <*> pIdentifier
  
pBTerm :: Parser ParsedExpr
pBTerm = pParenExpr <|> pVar

pBExpr :: Parser ParsedExpr
pBExpr = makeExprParser pBTerm boolOperatorTable 

binaryBool :: Parser () -> Op -> Operator Parser ParsedExpr
binaryBool parser op = InfixL (BExprAnn <$> getSourcePos <*> pure op <* parser)

boolOperatorTable :: [[Operator Parser ParsedExpr]]
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

symbol' :: Text -> Parser Text
symbol' = L.symbol sc

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
