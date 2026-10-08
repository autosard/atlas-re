{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Options.Applicative
import System.Console.ANSI.Codes
import Control.Monad.IO.Class (MonadIO (..))
import System.IO
import Data.Map(Map)
import qualified Data.Map as M
import System.Exit
import Data.Text(Text)
import System.FilePath
import qualified Data.Text.IO as TextIO
import qualified Data.Text.Lazy.IO as TextLazyIO
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import Data.Maybe(fromMaybe, catMaybes)
import System.Directory
import Data.Set(Set)
import qualified Data.Set as S
import Data.Tree(drawTree)
import Data.List(intercalate, dropWhileEnd, isPrefixOf)
import Data.Char(isSpace)
import Numeric(showFFloat)
import GHC.Clock(getMonotonicTime)
import Control.Exception(catches, Handler(..), ErrorCall(..), throwIO)
import System.IO.Error(isUserError, ioeGetErrorString)
import System.Environment(lookupEnv)
import System.Console.ANSI(hSupportsANSI)

import Syntax (Id)
import Syntax.PrettyPrint (prettyPrint)
import Syntax.Program
import Parsing.Tactic
import CostAnalysis.Coeff
import CostAnalysis.Analysis
import CostAnalysis.ProveMonad (ProofEnv(..), OptBound (OptBound), AnalysisMode (..))
import CostAnalysis.Tactic
import CostAnalysis.PrettyProof




import Cli(Options(..),
           AnalyzeOptions(..),
           EvalOptions(..),
           BenchOptions(..),
           Command(..), cliP)

import System.Random (getStdGen)
import Loading (loadProgram)

--import CostAnalysis.Constraint (Constraint)
import Control.Monad (when, unless)

-- import Benchmark(sort, genBenchmark, median)
import Control.Concurrent (yield)


app :: Options -> IO ()
app options = do
  case optCommand options of
    Analyze runOptions -> run options runOptions
    -- Eval evalOptions -> eval options evalOptions
    -- Bench benchOptions -> bench options benchOptions

run :: Options -> AnalyzeOptions -> IO ()
run Options{..} AnalyzeOptions{..} = do
  let (modName, fn) = case target of
        (Left mod) -> (mod, Nothing)
        (Right (mod, fn)) -> (mod, Just fn)
  -- When the potential measures are inferred as well, the amortised costs are
  -- unbounded: scaling the potential shifts costs between the functions, so
  -- that minimising them is ill-posed. Potentials are therefore only inferred
  -- for given signatures.
  when (switchInferPotential && analysisMode == Infer) $
    failWith "--infer-potential is only supported with --analysis-mode check."
  status "Loading" (T.unpack modName)
  prog <- loadProgram searchPath modName fn
  when switchPrintProg $ liftIO $ putStrLn (prettyPrint prog)

  let fns = M.keys (_pFunDefs prog)
  case fn of
    Just name | not (M.member name (_pFunDefs prog)) -> do
      -- the loaded program only contains the target and its dependencies
      available <- M.keys . _pFunDefs <$> loadProgram searchPath modName Nothing
      failWith $ "Module '" ++ T.unpack modName ++ "' does not define function '" ++ T.unpack name ++ "'."
        ++ (if null available then "" else "\nAvailable functions: " ++ commaList available)
    _ -> return ()
  tactics <- case tacticsPath of
    Just path -> loadTactics (T.unpack modName) fns path
    Nothing -> return M.empty
  let env = ProofEnv {
        _tactics=tactics
        , _analysisMode=analysisMode
        , _incremental=switchIncremental
        , _costModes=analysisModes . _pConfig $ prog
        , _inferPotential=switchInferPotential
        , _axioms = _pAxioms prog
        , _outputDir = outputPath
        }
  status "Analyzing" $ case fns of
    [] -> "no functions"
    _ -> show (length fns) ++ plural (length fns) " function" ++ ": " ++ commaList fns
  removeInstances outputPath
  start <- getMonotonicTime
  result <- liftIO $ analyzeProgram env prog
  elapsed <- subtract start <$> getMonotonicTime
  proofFile <- writeHtmlProof outputPath result
  let took = " (" ++ showFFloat (Just 1) elapsed "s)"
  case _arResult result of
    Left _ -> do
      failed <- styled stderr [SetColor Foreground Vivid Red, SetConsoleIntensity BoldIntensity] "No proof found"
      hPutStrLn stderr $ failed ++ ": the constraint system is unsatisfiable" ++ took ++ "."
      hPutStrLn stderr "The unsat core is highlighted in the proof."
      putStrLn $ "Proof: " ++ proofFile
      exitWith (ExitFailure 1)
    Right (solution, OptBound objective) -> do
      ok <- styled stderr [SetColor Foreground Vivid Green, SetConsoleIntensity BoldIntensity] "Proof found"
      hPutStrLn stderr $ ok ++ took ++ "."
      when switchDumpCoeffs $ printSolutionCoeffs solution
      when switchPrintObjective $ putStrLn ("Objective: " ++ objective)
      putStrLn $ "Proof: " ++ proofFile

-- | Progress message on stderr, so that stdout only carries results.
status :: String -> String -> IO ()
status verb msg = do
  verb' <- styled stderr [SetConsoleIntensity BoldIntensity] (verb ++ replicate (10 - length verb) ' ')
  hPutStrLn stderr (verb' ++ msg)

warn :: String -> IO ()
warn msg = do
  prefix <- styled stderr [SetColor Foreground Vivid Yellow, SetConsoleIntensity BoldIntensity] "warning:"
  hPutStrLn stderr (prefix ++ " " ++ msg)

failWith :: String -> IO a
failWith msg = do
  prefix <- styled stderr [SetColor Foreground Vivid Red, SetConsoleIntensity BoldIntensity] "error:"
  hPutStrLn stderr (prefix ++ " " ++ dropWhileEnd isSpace msg)
  exitFailure

-- | Wraps the string in the given SGR codes, if the handle is a terminal and NO_COLOR is not set.
styled :: Handle -> [SGR] -> String -> IO String
styled h sgr s = do
  noColor <- maybe False (not . null) <$> lookupEnv "NO_COLOR"
  ansi <- hSupportsANSI h
  return $ if ansi && not noColor
    then setSGRCode sgr ++ s ++ setSGRCode [Reset]
    else s

commaList :: [Id] -> String
commaList = intercalate ", " . map T.unpack

plural :: Int -> String -> String
plural 1 s = s
plural _ s = s ++ "s"

printSolutionCoeffs solution = mapM_ (\(q, v) -> putStrLn $ show q ++ " = " ++ show v) (M.assocs solution)

-- | Remove the SMT instances of a previous run, so that the output directory
-- only holds the instances of the current one.
removeInstances :: FilePath -> IO ()
removeInstances path = do
  exists <- doesDirectoryExist path
  when exists $ do
    files <- listDirectory path
    mapM_ (removeFile . (path </>))
      [f | f <- files, "instance" `isPrefixOf` f, takeExtension f == ".smt"]

writeHtmlProof :: FilePath -> AnalysisResult -> IO String
writeHtmlProof path result = do
  sources <- M.fromList <$> mapM (\f -> (,) f . T.lines <$> TextIO.readFile f) (proofSourceFiles result)
  let html = renderProofWithSources sources result
  path <- liftIO $ makeAbsolute path
  liftIO $ createDirectoryIfMissing True path
  liftIO $ TextLazyIO.writeFile (path </> "index.html") html
  liftIO $ TextLazyIO.writeFile (path </> "style.css") css
  liftIO $ TextLazyIO.writeFile (path </> "proof.js") js
  return $ "file://" ++ path </> "index.html"


loadTactics :: String -> [Id] -> FilePath -> IO (Map Id Tactic)
loadTactics modName fns path = do
  loaded <- mapM loadOne fns
  let missing = [fn | (fn, Nothing) <- zip fns loaded]
  unless (null missing) $
    warn $ "No tactic file for " ++ commaList missing
      ++ " (looked for " ++ path </> modName </> "<function>.txt)."
  return $ M.fromList (catMaybes loaded)
  where loadOne :: Id -> IO (Maybe (Id, Tactic))
        loadOne fn = do
          let fileName = path </> modName </> T.unpack fn <.> "txt"
          exists <- doesFileExist fileName
          if exists then do
            contents <-TextIO.readFile fileName
            return $ Just (fn, parseTactic fileName contents)
          else return Nothing


main :: IO ()
main = do
  options <- execParser cliP
  app options `catches`
    [ Handler (\e -> throwIO (e :: ExitCode))
    , Handler (\e -> failWith $ if isUserError e then ioeGetErrorString e else show e)
    , Handler (\(ErrorCall msg) -> failWith msg) ]

