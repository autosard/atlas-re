{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE StrictData #-}

module Cli(Options(..),
           Command(..),
           AnalyzeOptions(..),
           optionsP,
           EvalOptions(..),
           BenchOptions(..),
           cliP) where

import Syntax (Fqn)

import Options.Applicative
import qualified Data.Text as T
import Data.Text (Text)
import Data.Char (isLower)
import CostAnalysis.ProveMonad (AnalysisMode(..))

data Options = Options
  { searchPath :: !(Maybe FilePath)
  , optCommand :: !Command
  }

data Command = Analyze !AnalyzeOptions
  | Eval !EvalOptions
  | Bench !BenchOptions

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
   -- the eval and bench commands are currently not implemented
   optCommand <- hsubparser (command "analyze"
                             (info analyzeCommandP (progDesc "Perform amortized resource analysis for the given functions.")))
   return Options{..}

data AnalyzeOptions = AnalyzeOptions {
  target :: Either Text Fqn,
  tacticsPath :: Maybe FilePath,
  outputPath :: FilePath,
  analysisMode :: AnalysisMode,
  switchIncremental :: Bool,
  switchPrintProg :: Bool,
  switchPrintObjective :: Bool,
  switchDumpCoeffs :: Bool,
  switchInferPotential :: Bool}

runOptionsP :: Parser AnalyzeOptions
runOptionsP = do
  tacticsPath <- optional $ strOption
    (long "tactics"
     <> short 't'
     <> metavar "PATH"
     <> help "When present, tactics will be loaded from this directory.")
  outputPath <- strOption
    (long "output"
     <> short 'o'
     <> metavar "DIR"
     <> help "Write the HTML proof to DIR."
     <> value "out"
     <> showDefault)
  analysisMode <- option (eitherReader parseAnalysisMode)
    (long "analysis-mode"
    <> metavar "MODE"
    <> help "Analysis mode. One of [check, infer]. (default: check)"
    <> value Check)
  switchIncremental <- switch
    (long "incremental"
    <> help "When active, individual constraint systems for each recursive binding group are solved incrementally.")
  switchPrintProg <- switch
    (long "print-program"
    <> help "Output the normalized program.")
  switchDumpCoeffs <- switch
    (long "dump-coeffs"
    <> help "Dump the values of found coefficients.")
  switchInferPotential <- switch
    (long "infer-potential"
    <> help "Ignore given potential functions and infer them instead.")
  switchPrintObjective <- switch
    (long "print-objective"
    <> help "Output the final value of the objective function.")      
  target <- argument (eitherReader parseFqn) (metavar "MODULE[.FUNCTION]" <> help "Analysis target, e.g. Heap.Splay or Heap.Splay.insert. When a specific function is specified only this function and its dependencies are analyzed, which can save time.")
  return AnalyzeOptions{..}

analyzeCommandP :: Parser Command
analyzeCommandP = Analyze <$> runOptionsP

parseAnalysisMode :: String -> Either String AnalysisMode
parseAnalysisMode "check" = Right Check
parseAnalysisMode "infer" = Right Infer
parseAnalysisMode s = Left $ "'" ++ s ++ "' is not a valid analysis mode. Use one of [check, infer]."

parseFqn :: String -> Either String (Either Text Fqn)
parseFqn s = case breakEnd (== '.') s of
               (_, []) -> Left errorMsg
               ([], _) -> Right (Left $ T.pack s)
               (prefix, name@(c:_))
                 | isLower c || c == '_' -> Right (Right (T.pack (init prefix), T.pack name))
                 | otherwise -> Right (Left $ T.pack s)
  where breakEnd p xs = let (a, b) = break p (reverse xs) in (reverse b, reverse a)
        errorMsg = "Could not parse fqn '" ++ s ++
                   "'. Make sure to specify the target name with <module>[.<function>]."


data EvalOptions = EvalOptions { modName :: !Text, expr :: !Text }

evalOptionsP :: Parser EvalOptions
evalOptionsP = EvalOptions
  <$> argument str (metavar "MODULE")
  <*> argument str (metavar "EXPR")

evalCommandP :: Parser Command
evalCommandP = Eval <$> evalOptionsP


data BenchOptions = BenchOptions { benchMod :: !Text, benchmark :: !Text, samples:: !Int }

benchOptionsP :: Parser BenchOptions
benchOptionsP = do
  benchMod <- argument str (metavar "MODULE")
  benchmark <- argument str (metavar "BENCHMARK")
  samples <- option auto (long "samples"
                           <> short 'n'
                           <> metavar "N"
                           <> help "Run N samples and return the median."
                           <> value 1
                           <> showDefault)
  return $ BenchOptions{..}

benchCommandP :: Parser Command
benchCommandP = Bench <$> benchOptionsP

