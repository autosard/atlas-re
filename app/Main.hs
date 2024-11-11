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
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential
import Ast(Module(..), TypedModule, TypedExpr, Fqn, defs, printProg)
import CostAnalysis.PrettyProof(renderProof, css, js)


import Colog (cmap, fmtMessage, logTextStdout, logWarning,
              usingLoggerT, logError, LoggerT, Msg, Severity)


import System.Environment(lookupEnv)

import Typing.Inference(inferExpr, inferModule)
import Normalization(normalizeMod, normalizeExpr)
import Parsing.Program(parseExpr)
import Parsing.Tactic
import Eval(evalWithModule)
import Primitive(Id)
import CostAnalysis.Tactic 
import CostAnalysis.ProveMonad
import CostAnalysis.Rules
import CostAnalysis.Analysis

import Cli(Options(..), RunOptions(..), EvalOptions(..), Command(..), cliP)

import System.Random (getStdGen)
import Module (load)
import SourceError (printSrcError)
import CostAnalysis.Constraint (Constraint)
import Control.Monad (when)
import AstContext (contextualizeMod)

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

type App a = LoggerT (Msg Severity) IO a

app :: Options -> App ()
app options = do
  case optCommand options of
    Run runOptions -> run options runOptions
    Eval evalOptions -> eval options evalOptions

run :: Options -> RunOptions -> App ()
run Options{..} RunOptions{..} = do
  let (modName, _) = case target of
        (Left mod) -> (mod, Nothing)
        (Right (mod, fn)) -> (mod, Just fn)
  (normalizedProg, contents) <- liftIO $ loadMod searchPath target
  let positionedProg = contextualizeMod normalizedProg
  when switchPrintProg $ liftIO $ putStrLn (printProg positionedProg)
  when (null . mutRecGroups $ positionedProg) $ do
    logError $ "Module does not define the requested function."
    liftIO exitFailure
  tactics <- case tacticsPath of
    Just path -> loadTactics (T.unpack modName) (M.keys (defs normalizedProg)) path
    Nothing -> return M.empty
  let env = ProofEnv {
        _tactics=tactics,
        _analysisMode=analysisMode,
        _incremental=switchIncremental}
  result <- liftIO $ analyzeModule env positionedProg
  
  case result of
    Left srcErr -> liftIO $ die $ printSrcError srcErr contents
    Right solverResult -> case solverResult of
      (deriv, _, Left unsatCore) -> let core' = S.fromList unsatCore in do
        logError "solver returned unsat. See unsat-core for details."
        liftIO $ writeHtmlProof "./out" (renderProof (Just core') deriv)
      (deriv, sig, Right (solution, pots)) -> do
        liftIO $ writeHtmlProof "./out" (renderProof Nothing deriv)
        liftIO $ printSolution switchDumpCoeffs sig pots solution
        

printSolution :: Bool -> RsrcSignature -> PotFnMap -> Solution -> IO ()
printSolution dumpCoeffs sig potFns solution = do
  when dumpCoeffs $ (do
                        mapM_ (\(q, v) -> putStrLn $ show q ++ " = " ++ show v) (M.assocs solution)
                        putStrLn "")
  putStrLn "Potential functions:"
  mapM_ printPotFn (M.assocs potFns)
  putStrLn ""
  mapM_ printFnBound (M.keys sig)
  where printFnBound fn = do
          let fnSig = sig M.! fn
          putStrLn $ T.unpack fn ++ ":"
          putStrLn $ "\t" ++ printBound potFns (withCost fnSig) solution
        printPotFn (kind, (pot, rhs)) = do
          putStrLn $ "\t" ++ printRHS pot rhs solution ++ " (" ++ show kind ++ ")"
          

writeHtmlProof :: FilePath -> LT.Text -> IO ()
writeHtmlProof path html = do
  path <- liftIO $ makeAbsolute path
  liftIO $ createDirectoryIfMissing False path
  liftIO $ TextLazyIO.writeFile (path </> "index.html") html
  liftIO $ TextLazyIO.writeFile (path </> "style.css") css
  liftIO $ TextLazyIO.writeFile (path </> "proof.js") js
  liftIO $ putStrLn $ "Saved proof to \"file://" ++ path </> "index.html" ++ "\""

printDeriv :: Bool -> Maybe (Set Constraint) -> Derivation -> IO ()
printDeriv showCs unsatCore deriv = putStr (drawTree deriv')
  where integrateCore = case unsatCore of
                          Just core -> Just (core, red)
                          Nothing -> Nothing 
        deriv' = fmap (printRuleApp showCs integrateCore) deriv

red :: String -> String
red s = setSGRCode [SetColor Foreground Vivid Red] ++ s ++ setSGRCode [Reset]

eval :: Options -> EvalOptions -> App ()
eval Options{..} EvalOptions{..} = do
  (mod, _) <- liftIO $ loadMod searchPath (Left modName)
  expr' <- liftIO $ loadExpr expr mod
  rng <- liftIO getStdGen
  let val = evalWithModule mod expr' rng
  liftIO $ print val


loadExpr :: Text -> TypedModule -> IO TypedExpr
loadExpr contents ctx = do
  let parsed = parseExpr contents
  typed <- case inferExpr ctx parsed of
        Left srcErr -> die $ printSrcError srcErr contents
        Right expr -> return expr
  return $ normalizeExpr typed

loadTactics :: String -> [Id] -> FilePath -> App (Map Id Tactic)
loadTactics modName fns path = M.fromList . catMaybes <$> mapM loadOne fns
  where loadOne :: Id -> App (Maybe (Id, Tactic))
        loadOne fn = do
          let fileName = path </> modName </> T.unpack fn <.> "txt"
          exists <- liftIO $ doesFileExist fileName
          if exists then do
            contents <- liftIO $ TextIO.readFile fileName
            return $ Just (fn, parseTactic fileName contents)
          else do
            logWarning $ "No tactic file for function '" `T.append` fn `T.append` "' found."
            return Nothing

loadMod :: Maybe FilePath -> Either Text Fqn -> IO (TypedModule, Text)
loadMod pathSearch modOrFqn = do
  searchPathfromEnv <- lookupEnv "ATLAS_SEARCH"
  let path = (`fromMaybe` pathSearch) . (`fromMaybe` searchPathfromEnv) $ "."
  (parsedMod, contents) <- case modOrFqn of
    Left moduleName -> load path moduleName Nothing
    Right (mod, fn) -> load path mod (Just fn)
  typedMod <- case inferModule parsedMod of
        Left srcErr -> die $ printSrcError srcErr contents
        Right mod -> return mod
  return (normalizeMod typedMod, contents)

main :: IO ()
main = do
  let logAction = cmap fmtMessage logTextStdout
  options <- execParser cliP
  usingLoggerT logAction $ app options

