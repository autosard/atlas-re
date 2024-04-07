{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ApplicativeDo #-}

module Cli(Options(..), Command(..), RunOptions(..), optionsP) where

import Module(Fqn)

import Options.Applicative

data Options = Options
  { searchPath :: Maybe FilePath
  , optCommand :: Command
  }

newtype Command = Run RunOptions

optionsP :: Parser Options
optionsP = do
   searchPath <- optional $ strOption
    (long "search"
     <> short 's'
     <> metavar "PATH"
     <> help "Search for modules in PATH.")
   optCommand <- hsubparser
     (command "run" 
       (info runCommandP (progDesc "Run type inference the given functions.")))
   return Options{..}

newtype RunOptions = RunOptions { fqns :: [Fqn] }

runOptionsP :: Parser RunOptions
runOptionsP = RunOptions <$> some (argument (eitherReader parseFqn) (metavar "FQN..."))

runCommandP :: Parser Command
runCommandP = Run <$> runOptionsP

  
parseFqn :: String -> Either String Fqn
parseFqn s = case suffix of
               [] -> Left errorMsg
               [_] -> Left errorMsg
               (_:functionName) -> Right (moduleName, functionName)
  where (moduleName, suffix) = break (== '.') s
        errorMsg = "Could not parse fqn '" ++ s ++
                   "'. Make sure to specify the module name with <module>.<function>."
