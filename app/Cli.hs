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
   -- the bench command is currently not implemented
   optCommand <- hsubparser (command "analyze"
                             (info analyzeCommandP (progDesc "Perform amortized resource analysis for the given functions."))
                             <> command "eval"
                             (info evalCommandP (progDesc "Evaluate expressions and report the incurred cost (ticks).")))
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
  switchPolyBounds :: Bool,
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
  switchPolyBounds <- switch
    (long "poly-bounds"
    <> help "Show bounds as polynomials in the sizes instead of binomial coefficients, e.g. ½·|l|² + ½·|l| instead of binom(|l|, 1) + binom(|l|, 2).")
  switchInferPotential <- switch
    (long "infer-potential"
    <> help "Ignore given potential functions and infer them instead. Requires --analysis-mode check.")
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


data EvalOptions = EvalOptions
  { evalMod :: !Text
  , evalExprs :: ![Text]
  , evalSeed :: !(Maybe Int)
  , evalSamples :: !Int }

evalOptionsP :: Parser EvalOptions
evalOptionsP = do
  evalSeed <- optional $ option auto
    (long "seed"
     <> metavar "N"
     <> help "Seed of the random generator for coins.")
  evalSamples <- option auto
    (long "samples"
     <> short 'n'
     <> metavar "N"
     <> help "Evaluate each expression N times and report the mean cost (for programs with coins)."
     <> value 1
     <> showDefault)
  evalMod <- argument str (metavar "MODULE")
  evalExprs <- many $ argument str (metavar "EXPR..." <> help "Expressions to evaluate, e.g. 'isort (Cons 2 (Cons 1 Nil))'. Natural number literals denote Peano numbers. Without EXPR, expressions are read from stdin, one per line.")
  return EvalOptions{..}

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

