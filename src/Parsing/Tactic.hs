{-# LANGUAGE OverloadedStrings #-}

module Parsing.Tactic where

import CostAnalysis.Tactic
import CostAnalysis.Rules

import Text.Megaparsec
import Text.Megaparsec.Char ( space1 )
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void ( Void )
import Control.Monad(void)

import Data.Text(Text)

type Parser = Parsec Void Text 

pTactic :: Parser Tactic
pTactic = sc *> pRule <* eof

pRule :: Parser Tactic
pRule = pAtomic <|> pParens pNonAtomic 

pAtomic :: Parser Tactic
pAtomic = Rule Leaf [] <$ symbol "leaf" 
  <|> Rule Node [] <$ symbol "node"
  <|> Rule Cmp [] <$ symbol "cmp"
  <|> Rule Var [] <$ symbol "pair"
  <|> Rule App [] <$ symbol "app"
  <|> Hole <$ symbol "?"
  <|> Auto <$ symbol "_"
  <?> "rule"

pNonAtomic :: Parser Tactic
pNonAtomic = Rule Ite <$ symbol "ite" <*> count 2 pRule 
  <|> Rule Match <$ symbol "match" <*> many pRule
  <|> Rule Let <$ symbol "let" <*> count 2 pRule 
  <|> Rule TickNow <$ symbol "tick:now" <*> count 1 pRule
  <|> Rule TickDefer <$ symbol "tick:defer" <*> count 1 pRule
  <|> (do rule <- Weaken <$ symbol "w" <*> pRuleArgs
          Rule rule <$> count 1 pRule)
  <|> Rule Shift <$ symbol "shift" <*> count 1 pRule
  <?> "rule"

pRuleArg :: Parser RuleArg
pRuleArg = Mono <$ symbol "mono"
  <|> L2xy <$ symbol "l2xy"

pRuleArgs :: Parser [RuleArg]
pRuleArgs = do
  args <- optional (pCurlyParens (many pRuleArg))
  case args of
    Just args -> return args
    Nothing -> return []

pParens = between (symbol "(") (symbol ")")
pCurlyParens = between (symbol "{") (symbol "}")

symbol :: Text -> Parser ()
symbol = void . L.symbol sc

sc :: Parser ()
sc = L.space
  space1                        
  (L.skipLineComment "(*)")       
  (L.skipBlockComment "(*" "*)")

parseTactic :: String -> Text -> Tactic
parseTactic fileName contents = case runParser pTactic fileName contents of
  Left errs -> error $ errorBundlePretty errs
  Right tactic -> tactic

