{-# LANGUAGE RecordWildCards #-}

module SourceError where

import qualified Data.Text.IO as TextIO
import qualified Data.Text as T
import Text.Megaparsec.Pos

data SourceError = SourceError !SourcePos !String

printSrcError :: SourceError -> IO String
printSrcError (SourceError pos@SourcePos {..} error) = do
  let msg = "Error: " ++ sourcePosPretty pos ++ ": "
  contents <- TextIO.readFile sourceName
  let lines = T.lines contents
  let lineNum = unPos sourceLine
  let errorLine = T.unpack (lines !! (lineNum - 1))
  return $ msg ++ "\n\n" ++ show lineNum ++ " |" ++ errorLine ++ "\n\n" ++ error
  
