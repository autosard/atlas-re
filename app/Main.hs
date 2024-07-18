{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Options.Applicative
import Control.Monad.IO.Class (MonadIO (..))
import Data.Map(Map)
import qualified Data.Map as M
import System.Exit
import Data.Text(Text)
import System.FilePath
import qualified Data.Text.IO as TextIO
import qualified Data.Text as T
import Data.Maybe(fromMaybe, catMaybes)
import System.Directory
import Data.Set(Set)
import Data.Tree(drawTree)
import CostAnalysis.RsrcAnn

import Colog (cmap, fmtMessage, logTextStdout, logWarning,
              usingLoggerT, logError, LoggerT, Msg, Severity)


import System.Environment(lookupEnv)

import Typing.Inference(inferExpr, inferModule)
import Ast(TypedModule, TypedExpr)
import Normalization(normalizeMod, normalizeExpr)
import Parsing.Program(parseExpr, parseModule)
import Parsing.Tactic
import Eval(evalWithModule)
import StaticAnalysis(fns)
import Primitive(Id)
import CostAnalysis.Tactic 
import CostAnalysis.Potential.Log
import CostAnalysis.Deriv
import CostAnalysis.Solving

import Cli(Options(..), RunOptions(..), EvalOptions(..), Command(..), cliP)

import System.Random (getStdGen)
import Module (loadSimple)
import SourceError (printSrcError)
import CostAnalysis.Potential (printBound)
import CostAnalysis.Constraint (Constraint)

type App a = LoggerT (Msg Severity) IO a

app :: Options -> App ()
app options = do
  case optCommand options of
    Run runOptions -> run options runOptions
    Eval evalOptions -> eval options evalOptions

run :: Options -> RunOptions -> App ()
run Options{..} RunOptions{..} = do
  let (modName, funName) = fqn 
  (normalizedProg, contents) <- liftIO $ loadMod searchPath modName
  tactics <- case tacticsPath of
    Just path -> loadTactics (T.unpack modName) (fns normalizedProg) path
    Nothing -> return M.empty
  let _aRange = [0,1]
  let _bRange = [0,2]
  let args = Args _aRange _bRange _aRange _bRange (-1 : _bRange)
  let pot = logPot args
  let (varIdGen, proofResult) = runProof normalizedProg pot tactics
  (derivs, cs, sig) <- liftIO $ case proofResult of
        Left srcErr -> die $ printSrcError srcErr contents
        Right v -> return v
  solution <- liftIO $ solveZ3 pot sig cs varIdGen
--  liftIO $ putStr (printProg normalizedProg)
  --liftIO $ mapM (printDeriv (S.fromList cs)) derivs
  case solution of
    (Left _) -> logError "error"
    (Right coeffs) -> let target = withCost $ sig M.! funName in do
      --liftIO $ print solution 
      liftIO $ putStr (printBound pot target coeffs)
      

printDeriv :: Set Constraint -> (Id, Derivation) -> IO ()
printDeriv unsatCore (id, deriv) = putStr $ T.unpack id ++ ":\n\n" ++ drawTree deriv'
  where deriv' = fmap (printRuleApp unsatCore) deriv

eval :: Options -> EvalOptions -> App ()
eval Options{..} EvalOptions{..} = do
  (mod, _) <- liftIO $ loadMod searchPath modName
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

loadMod :: Maybe FilePath -> Text -> IO (TypedModule, Text)
loadMod pathSearch modName = do
  searchPathfromEnv <- lookupEnv "ATLAS_SEARCH"
  let path = (`fromMaybe` pathSearch) . (`fromMaybe` searchPathfromEnv) $ "."
  (fileName, contents) <- loadSimple path modName
  let parsedMod = parseModule fileName modName contents 
  typedMod <- case inferModule parsedMod of
        Left srcErr -> die $ printSrcError srcErr contents
        Right mod -> return mod
  return (normalizeMod typedMod, contents)

main :: IO ()
main = do
  let logAction = cmap fmtMessage logTextStdout
  options <- execParser cliP
  usingLoggerT logAction $ app options

