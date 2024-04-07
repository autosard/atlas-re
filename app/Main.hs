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

import qualified Iris
import qualified Options.Applicative as Opt


import Prelude hiding (readFile)
import Data.Text.IO(readFile, putStr)
import System.FilePath(FilePath)
import System.Environment(lookupEnv)


import qualified Parser
import qualified Module

import Cli

import qualified Paths_atlas_revisited as Autogen


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
      searchPathfromEnv <- liftIO $ lookupEnv "ATLAS_SEARCH"
      let path = (`fromMaybe` searchPath) . (`fromMaybe` searchPathfromEnv) $ "."
      liftIO $ putStrLn =<< Module.load path fqns
  

main :: IO ()
main = do
  Iris.runCliApp appSettings $ unApp app
  
