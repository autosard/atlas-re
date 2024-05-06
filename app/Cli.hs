{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ApplicativeDo #-}

module Cli(Options(..), Command(..), RunOptions(..), optionsP, EvalOptions(..)) where

import Ast(Fqn)

import Options.Applicative
import qualified Data.Text as T
import Data.Text (Text)

data Options = Options
  { searchPath :: !(Maybe FilePath)
  , optCommand :: !Command
  }

data Command = Run !RunOptions | Eval !EvalOptions

optionsP :: Parser Options
optionsP = do
   searchPath <- optional $ strOption
    (long "search"
     <> short 's'
     <> metavar "PATH"
     <> help "Search for modules in PATH.")
   optCommand <- hsubparser (command "run"
                             (info runCommandP (progDesc "Run type inference for the given functions.")))
                 <|> hsubparser (command "eval"
                                 (info evalCommandP (progDesc "Evaluate the given expression in the context of the given module.")))
   return Options{..}

newtype RunOptions = RunOptions { fqn :: Fqn }

runOptionsP :: Parser RunOptions
runOptionsP = RunOptions <$> argument (eitherReader parseFqn) (metavar "FQN")

runCommandP :: Parser Command
runCommandP = Run <$> runOptionsP

parseFqn :: String -> Either String Fqn
parseFqn s = case suffix of
               [] -> Left errorMsg
               [_] -> Left errorMsg
               (_:functionName) -> Right (T.pack moduleName, T.pack functionName)
  where (moduleName, suffix) = break (== '.') s
        errorMsg = "Could not parse fqn '" ++ s ++
                   "'. Make sure to specify the module name with <module>.<function>."


data EvalOptions = EvalOptions { modName :: !Text, expr :: !Text }

evalOptionsP :: Parser EvalOptions
evalOptionsP = EvalOptions
  <$> argument str (metavar "MODULE")
  <*> argument str (metavar "EXPR") 

evalCommandP :: Parser Command
evalCommandP = Eval <$> evalOptionsP
