{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Syntax.PrettyPrint
  ( PrettyPrint (..)
  , break
  , paren
  , printPos
  )where

import Prelude hiding (break)
import Data.List (intercalate)
import Text.Megaparsec (SourcePos, unPos, sourceLine, sourceColumn)
import Data.Ratio


class PrettyPrint a where
  prettyPrint :: a -> String

instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrint = intercalate ", " . map prettyPrint

instance PrettyPrint Rational where
  prettyPrint r
    | denominator r == 1 = show (numerator r)
    | otherwise          = show (numerator r) ++ "/" ++ show (denominator r) where
  
break :: Int -> String
break ident = "\n" ++ replicate (2*ident) ' '

paren :: String -> String
paren s = "(" ++ s ++ ")"

printPos :: SourcePos -> String
printPos pos = show (unPos . sourceLine $ pos) ++ ","  ++ show (unPos $ sourceColumn pos)
