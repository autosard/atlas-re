module CostAnalysis.TemplateLanguage where

import Data.Set(Set)

import Primitive(Id)
import Syntax.ResourceExpression


defaultLangConfig = [LogLang 1 2, BinomLang 2, RankLang]

data AtomicLang
  = SizeLang Int Int
  | LogLang Int Int
  | BinomLang Int
  | RankLang
  deriving Show

type TemplateLanguage = [Id] -> Set ResourceTerm



