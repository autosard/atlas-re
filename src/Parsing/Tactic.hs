{-# LANGUAGE OverloadedStrings #-}

module Parsing.Tactic where

import CostAnalysis.Tactic

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
pAtomic = Leaf <$ symbol "leaf"
  <|> Node <$ symbol "node"
  <|> Cmp <$ symbol "cmp"
  <|> Var <$ symbol "pair"
  <|> App <$ symbol "app"

pNonAtomic :: Parser Tactic
pNonAtomic = Ite <$ symbol "ite" <*> pRule <*> pRule
  <|> Match <$ symbol "match" <*> many pRule
  <|> Let <$ symbol "let" <*> pRule <*> pRule
  <|> TickNow <$ symbol "tick:now" <*> pRule
  <|> TickDefer <$ symbol "tick:defer" <*> pRule
  <|> Weaken <$ symbol "w" <*> pRuleArgs <*> pRule
  <|> Shift <$ symbol "shift" <*> pRule

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

parse :: String -> Text -> Tactic
parse fileName contents = case runParser pTactic fileName contents of
  Left errs -> error $ errorBundlePretty errs
  Right tactic -> tactic

