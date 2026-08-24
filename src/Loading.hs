{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Loading (loadProgram) where

import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Text.IO as TextIO(readFile)
import qualified Data.Text as T
import Data.Text(Text)
import Data.List(uncons)
import Data.Maybe(fromMaybe)
import Control.Monad.State
import Control.Monad.Extra
import qualified System.FilePath.Glob as Glob
import System.Environment(lookupEnv)
import SourceError (printSrcError)

import Syntax (Id, Positioned)
import Syntax.Surface
import Syntax.Program
import Parsing.Program(parseProgram)
import Typing (inferProgram)
import Normalization (normalizeProg)
import Contextualization (contextualizeProg)
import Elaboration (elabProgram)

extension = ".atl"

data ModuleState
  = NotVisited
  | Visiting    -- currently being processed
  | Visited     -- completely processed

newtype LoaderState = LoaderState {
  moduleStates :: Map Id ModuleState
}

getModState :: Text -> StateT LoaderState IO ModuleState
getModState modName = do
    states <- gets moduleStates
    return $ M.findWithDefault NotVisited modName states


buildProgram :: [SurfaceProgram] -> SurfaceProgram
buildProgram [] = error "No module loaded."
buildProgram (p:ps) = foldr go p ps
  where go p1 p2 = SurfaceProgram {
          sfSig = M.union (sfSig p1) (sfSig p2),
          sfConfig = mergeConfigs (sfConfig p1) (sfConfig p2),
          sfFunDefs = M.union (sfFunDefs p1) (sfFunDefs p2),
          sfDataDefs = sfDataDefs p1 ++ sfDataDefs p2,
          sfMeasureDefs = sfMeasureDefs p1 ++ sfMeasureDefs p2}
        mergeConfigs cfg1 cfg2 = ProgConfig
          { templateConfig = case templateConfig cfg1 of
              [] -> templateConfig cfg2
              nonEmpty -> templateConfig cfg1,
            analysisModes = M.union (analysisModes cfg1) (analysisModes cfg2)
          }
    
loadSurfaceProgram :: FilePath -> Text -> IO SurfaceProgram
loadSurfaceProgram loadPath initialMod = evalStateT go (LoaderState M.empty)
  where go = do
          mods <- loadModule loadPath initialMod
          return $ buildProgram mods

loadModule :: FilePath -> Text -> StateT LoaderState IO [SurfaceProgram]
loadModule loadPath name = do
  state <- getModState name
  case state of
    NotVisited -> do
      file <- liftIO $ findModule loadPath (T.unpack name)
      contents <- liftIO $ TextIO.readFile file
      let (prog, imports) = parseProgram file name contents
      (prog :) <$> concatMapM (loadModule loadPath) imports
    Visited -> return []
    Visiting -> fail $ "Import cycle detected involving " ++ show name



findModule :: String -> String -> IO FilePath
findModule loadPath moduleName = do
  matches <- Glob.glob $ loadPath ++ "/**/" ++ modulePath ++ extension
  case uncons matches of
    Nothing -> fail $ "Could not locate module '" ++ moduleName ++ "'. Please check the specified search path."
    Just (file,_) -> return file
    where modulePath = map (\c -> if c == '.' then '/' else c) moduleName 



loadProgram :: Bool -> Maybe FilePath -> Text -> Maybe Id -> IO (Program Positioned)
loadProgram ignorePot pathSearch modName fn = do
  searchPathfromEnv <- lookupEnv "ATLAS_SEARCH"
  let path = (`fromMaybe` pathSearch) . (`fromMaybe` searchPathfromEnv) $ "."
  surfaceProg <- loadSurfaceProgram path modName

  let run step = either printSrcError return . step

  contextualizeProg
    . normalizeProg
    <$> (run inferProgram
         =<< run (elabProgram ignorePot) surfaceProg)
