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


import Syntax.Ast
import Parsing.Tactic
import CostAnalysis.Coeff
import CostAnalysis.Analysis
import CostAnalysis.ProveMonad (ProofEnv(..))
import CostAnalysis.Tactic
import CostAnalysis.PrettyProof


import Primitive(Id, dbg)

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
  createDirectoryIfMissing True "out"
  let (modName, fn) = case target of
        (Left mod) -> (mod, Nothing)
        (Right (mod, fn)) -> (mod, Just fn)
  prog <- loadProgram searchPath modName fn
  when switchPrintProg $ liftIO $ putStrLn (printProg prog)

  unless (case fn of 
            Just name -> M.member name (_pFunDefs prog)
            Nothing -> True
         ) $ do
    fail "Module does not define the requested function."
  tactics <- case tacticsPath of
    Just path -> loadTactics (T.unpack modName) (M.keys (_pFunDefs (dbg "templ" (show .templateConfig . _pConfig )prog))) path
    Nothing -> return M.empty
  let env = ProofEnv {
        _tactics=tactics
        , _analysisMode=analysisMode
        , _incremental=switchIncremental
        }
  result <- liftIO $ analyzeProgram env prog
  case result of
    (AnalysisResult {_arResult=Left unsatCore}) ->
      let core' = S.fromList unsatCore in do
          hPutStrLn stderr "solver returned unsat. See unsat-core for details."
          writeHtmlProof "./out" (renderProof result) 
    (AnalysisResult {_arResult=(Right (solution, objective))}) -> do
        putStr "Done. "
        writeHtmlProof "./out" (renderProof result)
        when switchPrintObjective
          (do
              putStrLn ""
              putStrLn ("objective: " ++ objective))

printSolutionCoeffs solution = mapM_ (\(q, v) -> putStrLn $ show q ++ " = " ++ show v) (M.assocs solution)
-- printSolution :: Bool -> FreeSignature -> PotFnMap -> Map Coeff Rational -> IO ()
-- printSolution dumpCoeffs sig potFns solution = do
--   when dumpCoeffs (do
--                       mapM_ (\(q, v) -> putStrLn $ show q ++ " = " ++ show v) (M.assocs solution)
--                       putStrLn "")
--   putStrLn ""
--   putStrLn "potential functions:"
--   mapM_ printPotFn (M.assocs potFns)
--   putStrLn ""
--   mapM_ printFnBound (M.keys sig)
--   putStrLn ""
--   putStrLn "where (e1,...,en) := f x1 ... xm"
--   where printFnBound fn = do
--           let fnSig = sig M.! fn
--           putStrLn $ T.unpack fn ++ ":"
--           let CostSig s1 s2 = withCost fnSig
--           putStrLn $ "\t" ++ printBound potFns s1 solution
--           case s2 of
--             Just s -> putStrLn $ "\t" ++ printBound potFns s solution ++ " (worst case)"
--             Nothing -> putStr ""
--         printPotFn (kind, (pot, rhs)) = do
--           putStrLn $ "\t" ++ show kind ++ ": " ++ printRHS pot rhs solution 
          

writeHtmlProof :: FilePath -> LT.Text -> IO ()
writeHtmlProof path html = do
  path <- liftIO $ makeAbsolute path
  liftIO $ createDirectoryIfMissing False path
  liftIO $ TextLazyIO.writeFile (path </> "index.html") html
  liftIO $ TextLazyIO.writeFile (path </> "style.css") css
  liftIO $ TextLazyIO.writeFile (path </> "proof.js") js
  liftIO $ putStrLn $ "Saved proof to \"file://" ++ path </> "index.html" ++ "\""

-- printDeriv :: Bool -> Maybe (Set Constraint) -> Derivation -> IO ()
-- printDeriv showCs unsatCore deriv = putStr (drawTree deriv')
--   where integrateCore = case unsatCore of
--                           Just core -> Just (core, red)
--                           Nothing -> Nothing 
--         deriv' = fmap (printRuleApp showCs integrateCore) deriv

-- red :: String -> String
-- red s = setSGRCode [SetColor Foreground Vivid Red] ++ s ++ setSGRCode [Reset]

-- eval :: Options -> EvalOptions -> App ()
-- eval Options{..} EvalOptions{..} = do
--   (mod, _) <- liftIO $ loadMod searchPath (Left modName)
--   --expr' <- liftIO $ loadExpr expr mod
--   rng <- liftIO getStdGen
--   -- let val = evalWithModule mod expr' rng
--   --e <- liftIO $ genBenchmark "gtree" ["4"] mod
--   e <- liftIO $ genBenchmark "golden_delmin" ["4"] mod
--   let val = snd $ evalWithModule mod e rng
--   liftIO $ print val

-- bench :: Options -> BenchOptions -> App ()
-- bench Options{..} BenchOptions{..} = do
--   (mod, _) <- liftIO $ loadMod searchPath (Left benchMod)
--   let args = words $ T.unpack benchmark
--   expr <- liftIO $ genBenchmark (head args) (tail args) mod 
--   rng <- liftIO getStdGen
--   let (_, vs) = foldr (eval mod expr) (rng, []) [1..samples] 
--   let val = median vs
--   liftIO $ print val
--   where eval mod expr _ (rng, vs) = let (rng', v) = evalWithModule mod expr rng in
--           (rng', fst v : vs)


-- loadExpr :: Text -> TypedModule -> IO TypedExpr
-- loadExpr contents ctx = do
--   let parsed = parseExpr contents
--   typed <- case inferExpr ctx parsed of
--         Left srcErr -> die $ printSrcError srcErr contents
--         Right expr -> return expr
--   return $ normalizeExpr typed

loadTactics :: String -> [Id] -> FilePath -> IO (Map Id Tactic)
loadTactics modName fns path = M.fromList . catMaybes <$> mapM loadOne fns
  where loadOne :: Id -> IO (Maybe (Id, Tactic))
        loadOne fn = do
          let fileName = path </> modName </> T.unpack fn <.> "txt"
          exists <- doesFileExist fileName
          if exists then do
            contents <-TextIO.readFile fileName
            return $ Just (fn, parseTactic fileName contents)
          else do
            print $ "No tactic file for function '" `T.append` fn `T.append` "' found."
            return Nothing


main :: IO ()
main = do
  options <- execParser cliP
  app options

