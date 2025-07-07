{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module Parsing.Program(parseExpr, parseModule, initialPos, SourcePos) where

import Control.Monad 
import Control.Applicative hiding (many, some)

import Data.List(singleton, nub)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void ( Void )
import Control.Monad.Combinators.Expr
import Data.Char (isAlphaNum)
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Set as S
import Data.Set(Set)
import Data.Ratio((%))
import Data.Maybe(isJust, fromMaybe)
import Data.Functor(($>))
import Lens.Micro.Platform

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
import CostAnalysis.Annotation (FunAnn(..),
                                BoundAnn,
                                split)
import CostAnalysis.Template (BoundTemplate(..))
import CostAnalysis.Coeff (coeffArgs)

defaultCoinPropability :: Rational
defaultCoinPropability = 1 % 2

newtype ParserContext = ParserContext { ctxModuleName :: Text }
data ParserState = ParserState { _varIdGen :: Int,
                                 _typeVarMapping :: Map Id Type,
                                 _varIdentifiers :: Set Id}

makeLenses ''ParserState

quantifyTypeVar :: Id -> Parser Type
quantifyTypeVar id = do
  state <- get
  varMap <- use typeVarMapping
  lastId <- use varIdGen
  let nextId = lastId + 1
  case M.lookup id varMap of
    Nothing -> do
      let var = TGen lastId
      put state{
        _varIdGen = nextId,
        _typeVarMapping = M.insert id var varMap
        }
      return var
    Just var -> return var

type Parser = ParsecT Void Text (RWS ParserContext () ParserState)


pModule :: Parser (ModConfig, [ParsedFunDef])
pModule = sc *> do
  pots <- optional $ pPragma "POTENTIAL" pPotentialMapping
  rhsTerms <- optional $ pPragma "RHSTERMS" (return True)
  let config = ModConfig
        (fromMaybe M.empty pots)
        (fromMaybe False rhsTerms)
  (config,) <$> manyTill pFunc eof

pPragma :: Text -> Parser a -> Parser a
pPragma word p = between (try (symbol "{-#")) (symbol "#-}") $ symbol word *> p

pPotentialMapping :: Parser (Map Type PotentialKind)
pPotentialMapping = M.fromList <$> pParens (sepBy (do
  t <- pType
  symbol ":"
  pot <- pPotentialMode
  return (t, pot)) (symbol ","))

pPotentialMode :: Parser PotentialKind
pPotentialMode =
  try (symbol "loglrx") $> LogLRX
  <|> symbol "loglr" $> LogLR
  <|> symbol "polynomial" $> Polynomial
  <|> symbol "linlog" $> LinLog
  <|> symbol "logr" $> LogR
  <|> symbol "logl" $> LogL
  <|> symbol "log_golden" $> LogGolden
  <|> symbol "rank" $> Rank
   

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
  numCfs <- optional $ try (pPragma "NUMCF" pNumCf)
  strongCf <- optional $ pPragma "STRONGCF" (return True)
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
  varIdentifiers %= (\s -> foldr S.insert s args)
  let cfg = FnConfig numCfs (fromMaybe False strongCf)
  FunDef (ParsedFunAnn pos funFqn _type cost cfg) funName args <$> pExpr

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
  return $ Coeffs (FunAnn withCost (fromMaybe [] costFree) False)

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
             _varIdGen = 0,
             _typeVarMapping = M.empty
             })
  tArgs <- pArgsType
  pArrow
  tResult <- pType
  len <- use varIdGen
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


pFunResourceAnn :: Parser ((BoundAnn, BoundAnn), BoundAnn)
pFunResourceAnn = do
  from <- pTypedResourceAnn
  pArrow
  to <- pTypedResourceAnn
  let (from', fromRef) = split from to
  return ((from', fromRef), to)

pTypedResourceAnn :: Parser BoundAnn
pTypedResourceAnn = M.fromList <$> sepBy pResourceAnn (symbol ",")

pResourceAnn :: Parser (Type, BoundTemplate)
pResourceAnn = do
  t <- pType
  coeffs <- M.fromList <$> pSqParens pCoefficients
  let args = nub $ foldr (\i ids -> ids ++ coeffArgs i) [] (M.keys coeffs)
  return (t, BoundTemplate args coeffs)

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

pParenExpr :: Parser ParsedExpr
pParenExpr = pParens pExpr

pExpr :: Parser ParsedExpr
pExpr = try pParenExpr
  <|> pKeywordExpr
  <|> pInfixExpr 
  <?> "expression"

pKeywordExpr :: Parser ParsedExpr
pKeywordExpr
  = (do
        vars <- use varIdentifiers
        pos <- getSourcePos
        symbol "if"
        e1 <- pExpr
        symbol "then"
        e2 <- pExpr
        symbol "else"
        varIdentifiers %= const vars
        e3 <- pExpr
        return $ IteAnn pos e1 e2 e3)
  <|> MatchAnn <$> getSourcePos <* symbol "match" <*> (try pUndefVar <|> pExpr) <* symbol "with" <* symbol "|" <*> sepBy1 pMatchArm (symbol "|")
  <|> LetAnn <$> getSourcePos <* symbol "let" <*> pDefIdentifier <* symbol "=" <*> pExpr <* symbol "in" <*> pExpr
  <|> TickAnn <$> getSourcePos <* symbol "~" <*> optional pRational <*> pExpr
  <|> CoinAnn <$> getSourcePos <* symbol "coin" <*> ((pRational <?> "coin probability") <|> pure defaultCoinPropability)


pConst :: Parser ParsedExpr
pConst = do
  pos <- getSourcePos
  (name, args) <- (,) <$> symbol' "true" <*> pure []
    <|> (,) <$> symbol' "false" <*> pure []
    <|> (,) <$> symbol' "node" <*> count 3 pArg
    <|> (,) <$> symbol' "leaf" <*> pure []
    <|> (,) <$> symbol' "cons" <*> count 2 pArg
    <|> (,) <$> symbol' "error" <*> pure []
    <|> (,) <$> symbol' "weight" <*> count 1 pArg
    <|> (do
            n <- pNumber
            return (T.append "num#" (T.pack (show n)), []))
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
    <|> (do
            iden <- pIdentifier
            varIdentifiers %= (iden `S.insert`)
            return $ Alias pos iden)

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
  WildcardVar pos <$ symbol "_"
    <|> (do
            iden <- pIdentifier
            varIdentifiers %= (iden `S.insert`)
            return $ Id pos iden)

pApplication :: Parser ParsedExpr
pApplication = AppAnn <$> getSourcePos <*> pIdentifier <*> some pArg

pArg :: Parser ParsedExpr
pArg = 
  pConst
  <|> pParenExpr
  <|> try (pVar <* notFollowedBy (symbol "= " <|> pDoubleColon2))
  <|> try pApplication
  <?> "function argument"

pVar :: Parser ParsedExpr
pVar = do
  vars <- use varIdentifiers
  pos <- getSourcePos
  iden <- pIdentifier
  unless (iden `S.member` vars) (fail $ "Unknown variable " ++ T.unpack iden)
  return $ VarAnn pos iden 

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
      binaryApp (symbol' ">=") "GE",
      binaryApp (symbol' "<") "LT",
      binaryApp (symbol' "==" <|> symbol' "⩵") "EQ",
      binaryApp (symbol' ">") "GT",
      binaryApp (symbol' "+") "+",
      binaryApp (symbol' "-") "-"
    ]
  ]

keywords = [ "if", "then", "else", "match", "with", "let", "in"]

pDefIdentifier :: Parser Text
pDefIdentifier = do
  iden <- pIdentifier
  varIdentifiers %= (iden `S.insert`)
  return iden

pUndefVar :: Parser (Expr Parsed)
pUndefVar = do
  v@(VarAnn _ iden) <- pVar
  varIdentifiers %= (iden `S.delete`)
  return v

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

pNumber = NumVal <$> lexeme L.decimal

pInteger :: Parser Integer
pInteger = lexeme L.decimal

pRational :: Parser Rational
pRational = do
  sign <- maybe 1 (const (-1)) <$> optional (symbol "-")
  num <- pInteger
  symbol "/"
  den <- pInteger
  return $ (sign * num) % den

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

initState = ParserState 0 M.empty S.empty


parseModule :: String -> Text -> Text -> (ModConfig, [ParsedFunDef])
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


