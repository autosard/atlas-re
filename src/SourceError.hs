{-# LANGUAGE RecordWildCards #-}

module SourceError where

import qualified Data.Text as T
import Text.Megaparsec.Pos
import Data.Text

data SourceError = SourceError !SourcePos !String

printSrcError :: SourceError -> Text -> String
printSrcError (SourceError pos@SourcePos {..} error) contents = 
  let msg = "Error: " ++ sourcePosPretty pos ++ ": "
      lines = T.lines contents
      lineNum = unPos sourceLine
      errorLine = T.unpack (lines !! (lineNum - 1))
  in msg ++ "\n\n" ++ show lineNum ++ " |" ++ errorLine ++ "\n\n" ++ error
  
