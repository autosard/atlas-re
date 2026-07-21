{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Parsing.Program(parseExpr, parseProgram, initialPos, SourcePos) where

import Control.Monad 
import Control.Applicative hiding (many, some)

import Data.List(singleton)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void ( Void )
import Control.Monad.Combinators.Expr
import Data.Char (isAlphaNum)
import qualified Data.Map as M
import qualified Data.Set as S

import Data.Ratio((%))
import Data.Maybe(fromMaybe)
import Data.Functor(($>))

import Prelude hiding (LT, EQ, GT, LE)

import Text.Megaparsec
import Text.Megaparsec.Char ( space1, upperChar, lowerChar, hspace1, char, printChar )
import qualified Text.Megaparsec.Char.Lexer as L

import Syntax.Ast
import Typing.Type
import Typing.Scheme
import Primitive(Id)
import CostAnalysis.TemplateLanguage
import Syntax.Measure (Measure(Size, Potential))


--------------------------------------------------------------------------------
-- Parser Interface
--------------------------------------------------------------------------------

type Parser = Parsec Void Text

  
parseProgram :: String -> Text -> Text -> (SurfaceProgram, [Id])
parseProgram fileName moduleName contents = case runParser pProgram fileName contents of 
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog

parseExpr contents = case runParser (pExpr sc) (T.unpack name) contents of
  Left errs -> error $ errorBundlePretty errs
  Right prog -> prog
  where name = "<interactive>"

--------------------------------------------------------------------------------
-- Pragmas and Config
--------------------------------------------------------------------------------

pPragma :: Text -> Parser a -> Parser (Maybe a)
pPragma word p = optional $ between (symbol "{-#") (symbol "#-}") $ symbol word *> p

pAtomicLangConf :: Parser AtomicLangConfig
pAtomicLangConf =
  symbol "size" $> SizeLangConf 
  <|> symbol "log" *> pParens sc (LogLangConf <$> pInt <* symbol "," <*> pInt)
  <|> BinomLangConf <$ symbol "binom" <*> pParens sc pInt
  <|> RankLangConf <$ symbol "rank"

pTemplateLanguageConfig :: Parser (Maybe TemplateLanguageConfig)
pTemplateLanguageConfig = pPragma "TEMPLATE" (pSqParens (sepBy pAtomicLangConf (symbol ",")))

--------------------------------------------------------------------------------
-- Programs and Top Level Definitions
--------------------------------------------------------------------------------

data TopLevel
  = TLClause (Id, SurfaceClause)
  | TLSig (Id, SurfaceFunSig)
  | TLData DataDecl
  | TLMeasure MeasureDef
  deriving Show

pTopLevel :: Parser TopLevel
pTopLevel = 
  TLData    <$> pDataDef
  <|> TLMeasure <$> pMeasureDef
  <|> TLSig     <$> try pFunSig
  <|> TLClause     <$> pSurfaceClause

pImport :: Parser Id
pImport = symbol "import" *> pUpperIdentifier

buildFunDefs ::
  M.Map Id SurfaceFunSig
  -> M.Map Id [SurfaceClause]
  -> Parser (M.Map Id SurfaceFunDef)
buildFunDefs sigs clauses =
  traverse build allNames
  where
    allNames =
      M.fromSet id $ M.keysSet sigs `S.union` M.keysSet clauses
    build name =
      case (M.lookup name sigs, M.lookup name clauses) of
        (Just sig, Just cls) ->
          return (SurfaceFunDef name cls)
        (Nothing, Just cls) ->
          -- inferred function
          return (SurfaceFunDef name cls)
        (Just _, Nothing) ->
          fail $ "Signature without definition: " ++ show name
        (Nothing, Nothing) ->
          fail "impossible"

pProgram :: Parser (SurfaceProgram, [Id])
pProgram = scn *> do
  templLangConfig <- pTemplateLanguageConfig
  
  let config = ProgConfig (fromMaybe defaultLangConfig templLangConfig)

  imports <- many pImport

  tops <- L.nonIndented sc (manyTill pTopLevel eof)

  let sigs = M.fromList [(fn, s) | TLSig (fn,s) <- tops]
      clauses :: [(Id, SurfaceClause)]
      clauses = [c | TLClause c <- tops]
      groupedClauses = M.fromListWith (++) (map (\(i, c) -> (i, [c])) clauses)
      
  funDefs <- buildFunDefs sigs groupedClauses
      
  return (SurfaceProgram
    { sfConfig   = config
    , sfSig     = sigs
    , sfFunDefs     = funDefs 
    , sfDataDefs    = [d | TLData d <- tops]
    , sfMeasureDefs = [m | TLMeasure m <- tops]
    }, imports)
  
--------------------------------------------------------------------------------
-- Data Definitions
--------------------------------------------------------------------------------

pDataDef :: Parser DataDecl
pDataDef = do
  pos <- getSourcePos
  symbol "data"
  name <- pUpperIdentifier
  params <- many pIdentifier
  symbol "="
  ctors <- sepBy pConstructorDecl (symbol "|")
  return $ DataDecl pos name params ctors

pConstructorDecl :: Parser CtorDecl
pConstructorDecl = do
  name <- pUpperIdentifier
  args <- many (pParens scn pType <|> try pType)
  return $ CtorDecl name args

  
--------------------------------------------------------------------------------
-- Measure Definitions
--------------------------------------------------------------------------------

buildMeasure :: Type -> Measure -> [(Id, SurfaceClause)] -> Parser MeasureDef
buildMeasure t measure namedClauses = do
  let (name, _) = head namedClauses
  let clauses = map snd namedClauses
  return $ MeasureDef t measure name clauses

pMeasureDef :: Parser MeasureDef
pMeasureDef = L.indentBlock sc $ do
  symbol "measure"
  measure <-   (symbol "Size" $> Size)
           <|> (symbol "Potential" $> Potential)
  ty <- pType
  hSymbol "where"
  return $ L.IndentSome Nothing (buildMeasure ty measure) pSurfaceClause

--------------------------------------------------------------------------------
-- Function Signatures
--------------------------------------------------------------------------------

pBindings :: Parser [(Id, Type)]
pBindings = try (pParens sc pBindInner)
  <|> pBindInner

pBindInner :: Parser [(Id, Type)]
pBindInner = sepBy ((,) <$> pIdentifier <* symbol ":" <*> pType) (symbol ",")

pResultBinding :: Parser (Id, Type)
pResultBinding = try (pParens sc single) <|> single
  where
    single = do
      x  <- pIdentifier
      _  <- symbol ":"
      ty <- pType
      return (x, ty)

pFunSig :: Parser (Id, SurfaceFunSig)
pFunSig = do
  name <- try pIdentifier <?> "function name"
  symbol ":"
  argBindings <- pBindings
  let tArgs = prod (map snd argBindings)
  symbol "|"
  costFrom <- pExpr sc
  pArrow
  resultBinding <- pResultBinding
  let tResult = snd resultBinding
  symbol "|"
  costTo <- pExpr sc
  return (name, SurfaceFunSig
    (quantifyAll (TFun tArgs tResult))
    SurfaceCostSig {
        scsFrom = (map fst argBindings, costFrom),
        scsTo = (fst resultBinding, costTo)})


--------------------------------------------------------------------------------
-- Function Definitions
--------------------------------------------------------------------------------

pClauseHead :: Parser (Text, [Pattern Parsed])
pClauseHead = do
  name <- pIdentifier
  args <- manyTill pPattern (symbol "=")
  return (name, args)

pSurfaceClause :: Parser (Id, SurfaceClause)
pSurfaceClause = L.lineFold scn $ \sc' -> do
  pos <- getSourcePos
  (name, args) <- pClauseHead
  body <- pExpr sc'
  scn
  return (name, SurfaceClause pos args body)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

pType :: Parser Type
pType = do
  TVar <$> pIdentifier
  <|> pProdType
  <|> pTypeApp

pTypeApp :: Parser Type
pTypeApp = do
  c <- pUpperIdentifier
  args <- many pType
  return (TAp c args)

pProdType :: Parser Type
pProdType = do
  ts <- pParens sc (sepBy1 pType pCross)
  return (prod ts)

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

pConstPattern :: SourcePos -> Parser (Pattern Parsed)
pConstPattern pos = do
  name <- pUpperIdentifier
  args <- many pPattern
  return $ PConst pos name args

pZeroAryConstPattern :: SourcePos -> Parser (Pattern Parsed)
pZeroAryConstPattern pos = do
  name <- pUpperIdentifier
  return $ PConst pos name []

pPattern :: Parser (Pattern Parsed)
pPattern = do
  pos <- getSourcePos
  pZeroAryConstPattern pos
    <|> pParens sc (pConstPattern pos)
    <|> PWildcard pos <$ symbol "_"
    <|> PVar pos <$> pIdentifier
    <|> pParens sc pPattern

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

pIfThenElse :: Parser () -> Parser (Expr Parsed)
pIfThenElse sc' = do
  pos <- getSourcePos
  symbol "if"
  e1 <- pExpr scn
  symbol "then"
  e2 <- pExpr scn
  symbol "else"
  e3 <- pExpr sc'
  return $ IteAnn pos e1 e2 e3

pMatchArm :: Parser () -> Parser (MatchArm Parsed)
pMatchArm sc' = MatchArmAnn <$> getSourcePos <* L.symbol sc' "|" <*> pPattern <* pArrow <*> (pExpr sc')

pMatch :: Parser () -> Parser (Expr Parsed)
pMatch sc' = do
  pos <- getSourcePos
  L.symbol sc' "match"
  arg <- pExpr sc' 
  L.symbol sc' "with"
  arms <- some (pMatchArm sc')
  return $ MatchAnn pos arg arms

defaultCoinPropability :: Rational
defaultCoinPropability = 1 % 2

pKeywordExpr :: Parser () -> Parser (Expr Parsed)
pKeywordExpr sc'
  = pIfThenElse sc'
  <|> pMatch sc'
  <|> LetAnn <$> getSourcePos <* symbol "let" <*> pIdentifier <* symbol "=" <*> pExpr sc' <* symbol "in" <*> pExpr sc'
  <|> TickAnn <$> getSourcePos <* symbol "~" <*> optional pRational <*> pExpr sc'
  <|> CoinAnn <$> getSourcePos <* symbol "coin" <*> ((pRational <?> "coin probability") <|> pure defaultCoinPropability)

pParenExpr :: Parser () -> Parser (Expr Parsed)
pParenExpr sc' = pParens sc (pExpr sc')

pZeroAryConst :: Parser () -> Parser (Expr Parsed)
pZeroAryConst sc' = ConstAnn <$> getSourcePos <*> pUpperIdentifier <*> pure []

pAtom :: Parser () -> Parser (Expr Parsed)
pAtom sc' = 
  pParenExpr sc'
  <|> pZeroAryConst sc'
  <|> pVar sc
  <|> pLiteral
  <?> "atomic expression"

pApplication :: Parser () -> Parser (Expr Parsed)
pApplication sc' = 
  AppAnn <$> getSourcePos <*> pIdentifier' sc' <*> sepEndBy1 (pAtom sc) (try sc')
  <|> (do 
          pos <- getSourcePos
          args <- singleton <$> between (symbol "|") (symbol "|")  (pAtom sc)
          return $ AppAnn pos "size" args
  )

pConst :: Parser () -> Parser (Expr Parsed)
pConst sc' = do
  pos <- getSourcePos
  (name, args) <- (,)
    <$> pUpperIdentifier' sc <*> sepEndBy (pAtom sc) (try sc')
    <|> ("(,)",) <$> try (pParens sc' ((\x y -> [x, y]) <$> pAtom sc' <* symbol "," <*> pAtom sc'))
  return $ ConstAnn pos name args

pVar :: Parser () -> Parser (Expr Parsed)
pVar sc' = VarAnn <$> getSourcePos <*> pIdentifier' sc'

pLiteral :: Parser (Expr Parsed)
pLiteral = do
  pos <- getSourcePos
  LitAnn pos <$> (
        LRat <$> try pRational
    <|> LNat <$> pNumber
    <|> LString <$> pString
    )

-- | Parses either a constructor application or a function application
pJuxtaposition :: Parser () -> Parser (Expr Parsed)
pJuxtaposition sc' = 
  try (pApplication sc')
  <|> pConst sc'
  <|> pVar sc'
  <|> pVar sc
  <|> pLiteral

binaryL :: Parser () -> Text -> Operator Parser (Expr Parsed)
binaryL sc op = InfixL (mk sc op)

-- binaryR :: Parser () -> Text -> Operator Parser (Expr Parsed)
-- binaryR sc op = InfixR (mk sc op)

binaryN :: Parser () -> Text -> Operator Parser (Expr Parsed)
binaryN sc op = InfixN (mk sc op)

prefix :: Parser () -> Text -> Operator Parser (Expr Parsed)
prefix sc op = Prefix $ do
  pos <- getSourcePos
  L.symbol sc op
  pure $ \a -> AppAnn pos op [a]

mk :: Parser () -> Text -> Parser (Expr Parsed -> Expr Parsed -> Expr Parsed)
mk sc op = do
  pos <- getSourcePos
  try $ do L.symbol sc op
           notFollowedBy (L.symbol sc ">")
  pure $ \a b -> AppAnn pos op [a, b]  

operatorTable :: Parser () -> [[Operator Parser (Expr Parsed)]]
operatorTable sc =
  [
    [ prefix sc "negate" ]
  ,
    [ binaryL sc "*" ]

  , [ binaryL sc "+" 
    , binaryL sc "-" 
    ]
  ,
    [ binaryN sc "<=" 
    , binaryN sc ">=" 
    , binaryN sc "<"  
    , binaryN sc ">"  
    , binaryN sc "==" 
    ]
  ]

pInfixExpr :: Parser () -> Parser (Expr Parsed)
pInfixExpr sc = makeExprParser (pJuxtaposition sc) (operatorTable sc)

pExpr :: Parser () -> Parser (Expr Parsed)
pExpr sc = try (pParenExpr sc)
  <|> pKeywordExpr sc
  <|> pInfixExpr sc
  <?> "expression"

--------------------------------------------------------------------------------
-- Identifiers
--------------------------------------------------------------------------------

keywords = [ "data", "measure", "import", "if", "then", "else", "match", "with", "let", "in"]
  
pIdentifierLike :: Parser () -> Parser Char -> Parser Text
pIdentifierLike sc firstChar = try $ do
  ident <- L.lexeme sc (
    T.cons <$> firstChar
           <*> takeWhileP Nothing identChar
           <?> "identifier")
  if ident `elem` keywords
    then fail $ "Use of reserved keyword " ++ T.unpack ident
    else return ident
  where
    identChar x =
         isAlphaNum x
      || x == '_'
      || x == '\''
      || x == '.'

pIdentifier :: Parser Text
pIdentifier = pIdentifierLike scn lowerChar

pIdentifier' :: Parser () -> Parser Text
pIdentifier' sc' = pIdentifierLike sc' lowerChar

pUpperIdentifier :: Parser Text
pUpperIdentifier = pIdentifierLike scn upperChar

pUpperIdentifier' :: Parser () -> Parser Text
pUpperIdentifier' sc = pIdentifierLike sc upperChar

--------------------------------------------------------------------------------
-- Literals
--------------------------------------------------------------------------------

pString :: Parser Text
pString = T.pack <$ char '"' <*> manyTill printChar (char '"')

pInt :: Parser Int
pInt = do
  sign <- maybe 1 (const (-1)) <$> optional (symbol "-")
  num <- lexeme L.decimal
  return $ sign * num

pNumber = lexeme L.decimal

pInteger :: Parser Integer
pInteger = lexeme L.decimal

pRational :: Parser Rational
pRational = do
  num <- pInteger
  symbol "/"
  den <- pInteger
  return $ num % den

--------------------------------------------------------------------------------
-- Delimiters
--------------------------------------------------------------------------------

pParens sc = between (symbol "(") (L.symbol sc ")")
pSqParens = between (symbol "[") (symbol "]")
pArrow = symbol "->" <|> symbol "→"

pCross = symbol "⨯" <|> symbol "*"

symbol :: Text -> Parser ()
symbol = void . L.symbol scn

hSymbol :: Text -> Parser ()
hSymbol = void . L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme scn

--------------------------------------------------------------------------------
-- Whitespace
--------------------------------------------------------------------------------

sc :: Parser ()
sc = L.space
  hspace1
  (L.skipLineComment "(*)")       
  (L.skipBlockComment "(*" "*)")

scn :: Parser ()
scn = L.space
  space1                        
  (L.skipLineComment "(*)")       
  (L.skipBlockComment "(*" "*)")

