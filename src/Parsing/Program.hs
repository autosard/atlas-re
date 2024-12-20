{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections #-}

module Parsing.Program(parseExpr, parseModule, initialPos, SourcePos) where

import Control.Monad 
import Control.Applicative hiding (many, some)

import Data.List(singleton)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void ( Void )
import Control.Monad.Combinators.Expr
import Data.Char (isAlphaNum)
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Set as S
import Data.Ratio((%))
import Data.Maybe(isJust, fromMaybe)
import Data.Functor(($>))

import Prelude hiding (LT, EQ, GT, LE)

import Text.Megaparsec
import Text.Megaparsec.Char ( letterChar, space1 )
import qualified Text.Megaparsec.Char.Lexer as L

import Ast
import Typing.Type
import Typing.Scheme
import Control.Monad.RWS
import Primitive(Id)
import qualified CostAnalysis.Coeff as Coeff

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


pModule :: Parser (Map Type PotentialKind, [ParsedFunDef])
pModule = sc *> do
  pots <- optional $ try (pPragma "POTENTIAL" pPotentialMapping)
  (fromMaybe M.empty pots,) <$> manyTill pFunc eof

pPragma :: Text -> Parser a -> Parser a
pPragma word p = between (symbol "{-#") (symbol "#-}") $ symbol word *> p

pPotentialMapping :: Parser (Map Type PotentialKind)
pPotentialMapping = M.fromList <$> pParens (sepBy (do
  t <- pType
  symbol ":"
  pot <- pPotentialMode
  return (t, pot)) (symbol ","))

pPotentialMode :: Parser PotentialKind
pPotentialMode = symbol "logarithmic" $> Logarithmic
                 <|> symbol "polynomial" $> Polynomial
                 <|> symbol "linlog" $> LinLog

data Signature = Signature
  Id
  Scheme
  (Maybe CostAnnotation)

pNumCf :: Parser Int
pNumCf = do
  n <- pInt
  if n > 0 then return n else
    fail "Number of cf derivations need to be at least one."

pFunc :: Parser ParsedFunDef
pFunc = do
  pos <- getSourcePos
  numCfs <- optional $ pPragma "NUMCF" pNumCf
  sig <- optional pSignature
  funName <- pIdentifier
  (_type, cost) <- case sig of
    Just (Signature name _type costAnn) -> do
      when (funName /= name ) (fail $ "Signature for function '" ++ T.unpack name ++ "' must be followod by defining equation.")
      return (Just _type, costAnn)
    Nothing -> return (Nothing, Nothing)
  modName <- asks ctxModuleName
  let funFqn = (modName, funName)
  args <- manyTill pIdentifier (symbol "=")
  FunDef (ParsedFunAnn pos funFqn _type cost numCfs) funName args <$> pExpr

pSignature :: Parser Signature
pSignature = do
  name <- try pIdentifier <?> "function name"
  void pDoubleColon2
  constraints <- optional ((pConstraints <* pDoubleArrow) <?> "type constraint(s)")
  _type <- pFunctionType <?> "function type"
  costAnn <- optional $ pCoeffAnn <|> pCostAnn
  return $ Signature name _type costAnn

pCoeffAnn :: Parser CostAnnotation
pCoeffAnn = do
  symbol "|" 
  withCost <- pFunResourceAnn
  costFree <- optional $ pCurlyParens $ sepBy pFunResourceAnn (symbol ",")
  return $ Coeffs withCost (fromMaybe [] costFree)

pCostAnn :: Parser CostAnnotation
pCostAnn = do
  symbol "@"
  worstCase <- isJust <$> optional (symbol ">")
  Cost worstCase <$> pTypedResourceAnn
  
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
  <|> (`TAp` []) <$> (Base <$ symbol "Base")
  <|> TAp <$> (Tree <$ symbol "Tree") <*> (singleton <$> pType)
  <|> TAp <$> (List <$ symbol "List") <*> (singleton <$> pType)
  <|> TAp Prod <$> pParens (sepBy1 pType pCross)


pFunResourceAnn :: Parser FunRsrcAnn
pFunResourceAnn = (,) <$> pTypedResourceAnn <* pArrow <*> pTypedResourceAnn

pTypedResourceAnn :: Parser (Map Type (Map Coeff.CoeffIdx Rational))
pTypedResourceAnn = M.fromList <$> sepBy pResourceAnn (symbol ",")

pResourceAnn :: Parser (Type, Map Coeff.CoeffIdx Rational)
pResourceAnn = do
  t <- pType
  coeffs <- M.fromList <$> pSqParens pCoefficients
  return (t, coeffs)

pCoefficients :: Parser [(Coeff.CoeffIdx, Rational)]
pCoefficients =  sepBy pCoefficient (symbol ",")

pCoefficient :: Parser (Coeff.CoeffIdx, Rational)
pCoefficient = do
  index <- pCoeffIdx
  void pMapsTo
  coefficient <- try pRational <|> toRational <$> pInt
  return (index, coefficient)

pCoeffIdx :: Parser Coeff.CoeffIdx
pCoeffIdx = Coeff.Pure <$> pIdentifier
  <|> Coeff.mixed . S.fromList <$> pParens (sepBy pFactor (symbol ","))

pFactor :: Parser Coeff.Factor
pFactor = Coeff.Const <$> pInt
  <|> try (do id <- pIdentifier
              symbol "^"
              arg <- pInt
              return $ Coeff.Arg id [arg])
  <|> (do id <- pIdentifier
          symbol "^"
          Coeff.Arg id <$> pListInt)


pExpr :: Parser ParsedExpr
pExpr = pKeywordExpr
  <|> try pApplication
  <|> try pInfixExpr 
  <?> "expression"

pKeywordExpr :: Parser ParsedExpr
pKeywordExpr
  = pConst
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
    <|> (,) <$> symbol' "cons" <*> count 2 pArg
    <|> (,) <$> symbol' "error" <*> pure []
    <|> ("numLit", []) <$ pNumber 
    <|> ("nil",) <$ symbol "[]" <*> pure []
    <|> ("(,)",) <$> try (pParens ((\x y -> [x, y]) <$> pArg <* symbol "," <*> pArg))
  return $ ConstAnn pos name args
  
pMatchArm :: Parser ParsedMatchArm
pMatchArm = MatchArmAnn <$> getSourcePos <*> pPattern <* pArrow <*> pExpr

pPattern :: Parser ParsedPattern
pPattern = do
  pos <- getSourcePos
  pConstPattern pos 
    <|> WildcardPat pos <$ symbol "_"
    <|> Alias pos <$> pIdentifier

pConstPattern :: SourcePos -> Parser ParsedPattern
pConstPattern pos = do
  (name, args) <- (,) <$> symbol' "node" <*> count 3 pPatternVar
    <|> (,) <$> symbol' "leaf" <*> pure []
    <|> ("nil",) <$ symbol "[]" <*> pure []
    <|> (,) <$> symbol' "cons" <*> count 2 pPatternVar
    <|> ("(,)",) <$> try (pParens ((\x y -> [x, y]) <$> pPatternVar <* symbol "," <*> pPatternVar))
  return $ ConstPat pos name args

pPatternVar :: Parser ParsedPatternVar
pPatternVar = do
  pos <- getSourcePos
  WildcardVar pos <$ symbol "_" <|> (Id pos <$> pIdentifier)

pApplication :: Parser ParsedExpr
pApplication = AppAnn <$> getSourcePos <*> pIdentifier <*> some pArg

pArg :: Parser ParsedExpr
pArg = pParenExpr
  <|> pConst
  <|> try (pVar <* notFollowedBy (symbol "= " <|> pDoubleColon2))
  <?> "function argument"

pVar :: Parser ParsedExpr
pVar = VarAnn <$> getSourcePos <*> pIdentifier

pInfixExpr :: Parser ParsedExpr
pInfixExpr = makeExprParser pArg operatorTable 

binaryApp :: Parser Text -> Id -> Operator Parser ParsedExpr
binaryApp parser id = InfixL curryConst
  where curryConst :: Parser (ParsedExpr -> ParsedExpr -> ParsedExpr)
        curryConst = do
          f <- const
          return (\a1 a2 -> f [a1, a2])
        const :: Parser ([ParsedExpr] -> ParsedExpr)
        const = ConstAnn <$> getSourcePos <* parser <*> pure id

operatorTable :: [[Operator Parser ParsedExpr]]
operatorTable =
  [
    [
      binaryApp (symbol' "<=") "LE",
      binaryApp (symbol' "<") "LT",
      binaryApp (symbol' "==" <|> symbol' "⩵") "EQ",
      binaryApp (symbol' ">") "GT"
    ]
  ]

keywords = [ "if", "then", "else", "match", "with", "let", "in"]

pIdentifier :: Parser Text
pIdentifier = do
  ident <- lexeme (T.cons <$> letterChar <*>
                   takeWhileP Nothing (\x -> isAlphaNum x || (x == '_') || (x == '\'') || (x == '.')) <?> "identifier")
           
  if ident `elem` keywords
    then fail $ "Use of reserved keyword " ++ T.unpack ident
    else return ident

pInt :: Parser Int
pInt = lexeme L.decimal

pListInt :: Parser [Int]
pListInt = pParens $ sepBy pInt (symbol ",")

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

initState = ParserState 0 M.empty


parseModule :: String -> Text -> Text -> (Map Type PotentialKind, [ParsedFunDef])
parseModule fileName moduleName contents = case fst $ evalRWS rws initEnv initState of
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog
  where initEnv = ParserContext moduleName
        rws = runParserT pModule fileName contents

parseExpr contents = case fst $ evalRWS rws initEnv initState of
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog
  where name = "<interactive>"
        initEnv = ParserContext name
        rws = runParserT pExpr (T.unpack name) contents


