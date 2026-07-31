{-# LANGUAGE RecordWildCards #-}

module SourceError where

import qualified Data.Text as T
import Text.Megaparsec.Pos
import qualified Data.Text.IO as TextIO(readFile)
import System.Exit

data SourceError e = SourceError !SourcePos e

printSrcError :: (Show a) => SourceError a -> IO b
printSrcError (SourceError pos@SourcePos {..} error) = do
  if sourceName == "<elab>" then 
    die (show error)
  else do
    contents <- TextIO.readFile sourceName
    die (buildMessage contents)
  where buildMessage contents =
          let msg = "Error: " ++ sourcePosPretty pos ++ ": "
              lines = T.lines contents
              lineNum = unPos sourceLine
              errorLine = T.unpack (lines !! (lineNum - 1))
              col = unPos sourceColumn
              gutter = show lineNum ++ " |"
              marker = replicate (length gutter + col - 1) ' ' ++ "^"
          in msg ++ "\n\n"
             ++ gutter
             ++ errorLine
             ++ "\n"
             ++ marker
             ++ "\n"
             ++ show error
  
