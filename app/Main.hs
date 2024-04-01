module Main where

import qualified Parser
import Prelude hiding (readFile)
import Data.Text.IO(readFile)

fileName = "examples/SplayTree.ml"

main :: IO ()
main = do
  prog <- Parser.run fileName <$> readFile fileName
  putStrLn $ show prog
  
