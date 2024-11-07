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
  target :: Either Text Fqn,
  tacticsPath :: Maybe FilePath,
  switchPrintDeriv :: Bool,
  analysisMode :: AnalysisMode,
  switchIncremental :: Bool,
  switchHideConstraints :: Bool,
  switchHtmlOutput :: Bool,
  switchPrintProg :: Bool,
  switchDumpCoeffs :: Bool}

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
  switchIncremental <- switch
    (long "incremental"
    <> help "When active, individual constraint systems for each recursive binding group are solved incrementally.")
  switchHideConstraints <- switch
    (long "hide-constraints"
    <> help "When active, only the derivation tree is printed without constraints.")
  switchHtmlOutput <- switch
    (long "html-output"
    <> help "When active, a html representation, potentially including the unsat-core is produced.")
  switchPrintProg <- switch
    (long "print-program"
    <> help "Output the normalized program.")
  switchDumpCoeffs <- switch
    (long "dump-coeffs"
    <> help "Dump the values of found coefficients.")      
  target <- argument (eitherReader parseFqn) (metavar "MODULE[.FUNCTION]" <> help "Analysis target. When a specific function is specified only this function and its dependencies are analyzed, which can save time.")
  return RunOptions{..}

runCommandP :: Parser Command
runCommandP = Run <$> runOptionsP

parseAnalysisMode :: String -> Either String AnalysisMode
parseAnalysisMode "check-coeffs" = Right CheckCoefficients
parseAnalysisMode "check-cost" = Right CheckCost
parseAnalysisMode "improve-cost" = Right ImproveCost
parseAnalysisMode "infer" = Right Infer
parseAnalysisMode _ = Left "not a valid inference mode"

parseFqn :: String -> Either String (Either Text Fqn)
parseFqn s = case suffix of
               [] -> Right (Left $ T.pack moduleName)
               [_] -> Left errorMsg
               (_:functionName) -> Right (Right (T.pack moduleName, T.pack functionName))
  where (moduleName, suffix) = break (== '.') s
        errorMsg = "Could not parse fqn '" ++ s ++
                   "'. Make sure to specify the target name with <module>[.<function>]."


data EvalOptions = EvalOptions { modName :: !Text, expr :: !Text }

evalOptionsP :: Parser EvalOptions
evalOptionsP = EvalOptions
  <$> argument str (metavar "MODULE")
  <*> argument str (metavar "EXPR") 

evalCommandP :: Parser Command
evalCommandP = Eval <$> evalOptionsP
