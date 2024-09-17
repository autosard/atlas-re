{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE StrictData #-}

module Cli(Options(..), Command(..), RunOptions(..), optionsP, EvalOptions(..), cliP) where

import Ast(Fqn)

import Options.Applicative
import qualified Data.Text as T
import Data.Text (Text)
import CostAnalysis.ProveMonad (AnalysisMode (CheckCoefficients, CheckCost, ImproveCost, Infer))
import CostAnalysis.Potential

data Options = Options
  { searchPath :: !(Maybe FilePath)
  , optCommand :: !Command
  }

data Command = Run !RunOptions | Eval !EvalOptions

cliP :: ParserInfo Options
cliP = info (optionsP <**> helper) ( fullDesc
  <> progDesc "A static analysis tool for Automated (Expected) Amortised Complexity Analysis."
  <> header "atlas - automated amortized complexity analysis" )

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

data RunOptions = RunOptions {
  fqn :: Fqn,
  tacticsPath :: Maybe FilePath,
  switchPrintDeriv :: Bool,
  analysisMode :: AnalysisMode,
  switchIncremental :: Bool,
  switchHideConstraints :: Bool,
  switchHtmlOutput :: Bool,
  potential :: PotentialMode}

runOptionsP :: Parser RunOptions
runOptionsP = do
  tacticsPath <- optional $ strOption
    (long "tactics"
     <> short 't'
     <> metavar "PATH"
     <> help "When present, tactics will be loaded from this directory.")
  switchPrintDeriv <- switch
    (long "print-deriv"
    <> help "Print the derivation tree in ascii.")
  analysisMode <- option (eitherReader parseAnalysisMode)
    (long "analysis-mode"
    <> help "Analysis mode. One of [check-coeffs, check-cost, improve-cost, infer]."
    <> value CheckCoefficients)
  potential <- option (eitherReader parsePotential)
    (long "potential"
    <> help "The type of potential function template used in the analysis. [logarithmic, polynomial]"
    <> value Logarithmic)
  switchIncremental <- switch
    (long "incremental"
    <> help "When active, individual constraint systems for each recursive binding group are solved incrementally.")
  switchHideConstraints <- switch
    (long "hide-constraints"
    <> help "When active, only the derivation tree is printed without constraints.")
  switchHtmlOutput <- switch
    (long "html-output"
    <> help "When active, a html representation, potentially including the unsat-core is produced.")  
  fqn <- argument (eitherReader parseFqn) (metavar "FQN")
  return RunOptions{..}

runCommandP :: Parser Command
runCommandP = Run <$> runOptionsP

parsePotential :: String -> Either String PotentialMode
parsePotential "logarithmic" = Right Logarithmic
parsePotential "polynomial" = Right Polynomial
parsePotential _ = Left "not a valid poential."

parseAnalysisMode :: String -> Either String AnalysisMode
parseAnalysisMode "check-coeffs" = Right CheckCoefficients
parseAnalysisMode "check-cost" = Right CheckCost
parseAnalysisMode "improve-cost" = Right ImproveCost
parseAnalysisMode "infer" = Right Infer
parseAnalysisMode _ = Left "not a valid inference mode"

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
