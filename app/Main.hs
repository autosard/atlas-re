{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}

module Main (main) where

import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Reader (MonadReader)
import Data.Maybe(fromMaybe)
import System.Exit
import Data.Text(Text)

import qualified Iris

import System.Environment(lookupEnv)

import Typing.Inference(inferExpr, inferModule)
import Ast(TypedModule, TypedExpr)
import Normalization(normalizeMod, normalizeExpr)
import Parsing.Program(parseExpr, parseModule)
import Eval(evalWithModule)

import Cli(Options(..), RunOptions(..), EvalOptions(..), Command(..), optionsP)

import qualified Paths_atlas_revisited as Autogen
import System.Random (getStdGen)
import Module (loadSimple)
import SourceError (printSrcError)


newtype App a = App
    { unApp :: Iris.CliApp Options () a
    } deriving newtype
        ( Functor
        , Applicative
        , Monad
        , MonadIO
        , MonadReader (Iris.CliEnv Options ())
        )

appSettings :: Iris.CliEnvSettings Options ()
appSettings = Iris.defaultCliEnvSettings
    { Iris.cliEnvSettingsHeaderDesc = "Atlas"
    , Iris.cliEnvSettingsProgDesc = "A static analysis tool for Automated (Expected) Amortised Complexity Analysis."
    , Iris.cliEnvSettingsVersionSettings =
        Just (Iris.defaultVersionSettings Autogen.version) {
        Iris.versionSettingsMkDesc = ("ATLAS v" <>)
        }
    , Iris.cliEnvSettingsCmdParser = optionsP
    }


app :: App ()
app = do
  Options{..} <- Iris.asksCliEnv Iris.cliEnvCmd
  case optCommand of
    Run RunOptions{..} -> do
      let (modName, funName) = fqn 
      normalizedProg <- liftIO $ loadMod searchPath modName
      liftIO $ print normalizedProg
    Eval EvalOptions{..} -> do
      mod <- liftIO $ loadMod searchPath modName
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
     

loadMod :: Maybe FilePath -> Text -> IO TypedModule
loadMod pathSearch modName = do
  searchPathfromEnv <- lookupEnv "ATLAS_SEARCH"
  let path = (`fromMaybe` pathSearch) . (`fromMaybe` searchPathfromEnv) $ "."
  (fileName, contents) <- loadSimple path modName
  let parsedMod = parseModule fileName modName contents 
  typedMod <- case inferModule parsedMod of
        Left srcErr -> die $ printSrcError srcErr contents
        Right mod -> return mod
  return $ normalizeMod typedMod

main :: IO ()
main = do
  Iris.runCliApp appSettings $ unApp app
  
