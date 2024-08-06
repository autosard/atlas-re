{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.AnnIdxQuoter(mix) where

import Text.Megaparsec
import Text.Megaparsec.Char (letterChar, space, char)
import Data.Void ( Void )
import Data.Char (isAlphaNum)
import Control.Monad(void)

import qualified Data.Set as S
import Data.Set(Set)

import qualified Text.Megaparsec.Char.Lexer as L

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import qualified CostAnalysis.Coeff as Coeff

data Atom = Lit !Int | Var !String | SetVar !String
data Factor = Atom !Atom | Arg !Atom !Atom

newtype Idx = Idx [Factor]



mix :: QuasiQuoter
mix = QuasiQuoter {
    quoteExp  = compile
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where notHandled things = error $
          things ++ " are not handled by the mix quasiquoter."

compile :: String -> Q Exp
compile s =
  case runParser pIdx "" s of
    Left  err    -> fail $ errorBundlePretty err
    Right (Idx []) -> [|Coeff.mixed (S.empty :: Set Coeff.Factor)|]
    Right (Idx factors) -> do
      let exps = map factorToQ factors
      appE (varE 'Coeff.mixed) $
            foldl1 (\x y -> appE (appE (varE 'S.union) x) y) exps

getName :: Exp -> Name
getName (VarE name) = name
getName _ = error "not a variable. This cannot happen."

factorToQ :: Factor -> Q Exp
factorToQ (Atom a@(Lit _)) = [| S.singleton (Coeff.Const $(atomToQ a)) |]
factorToQ (Atom a@(SetVar _)) = atomToQ a
factorToQ (Atom a@(Var _)) = [| S.singleton (Coeff.Const $(atomToQ a)) |]
factorToQ (Arg x y) = [| S.singleton (Coeff.Arg $(atomToQ x) $(atomToQ y)) |] 

atomToQ :: Atom -> Q Exp
atomToQ (Lit n) = [|n|]
atomToQ  (Var x) = dyn x
atomToQ (SetVar x) = dyn x

type Parser = Parsec Void String

pIdx :: Parser Idx
pIdx = Idx <$> sepBy pFactor (symbol ",") <* eof

pFactor :: Parser Factor
pFactor = try pArg <|> Atom <$> pAtom 

pArg :: Parser Factor
pArg = Arg <$> pAtom <* symbol "^" <*> pAtom

pAtom = Lit <$> pNumber <|>
        SetVar <$> pSetIdentifier <|>
        Var <$> pIdentifier 
  
symbol :: String -> Parser ()
symbol = void . L.symbol space

pNumber :: Parser Int
pNumber = lexeme L.decimal

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

pIdentifier :: Parser String
pIdentifier = lexeme pId

pSetIdentifier :: Parser String
pSetIdentifier = lexeme (char '_' *> pId )

pId :: Parser String
pId = (:) <$> letterChar <*> takeWhileP Nothing (\x -> isAlphaNum x || (x == '\'') ||(x == '_') || (x == '.')) <?> "identifier"
