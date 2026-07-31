{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}

module Loading where

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

import Primitive(Id, dbg)
import Syntax.Ast
import Parsing.Program(parseProgram)
import Typing.Inference (inferProgram)
import Syntax.Normalization (normalizeProg)
import Syntax.AstContext (contextualizeProg)
import Syntax.Elaboration (elabProgram)

extension = ".ml"

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
          sfConfig = sfConfig p2,
          sfFunDefs = M.union (sfFunDefs p1) (sfFunDefs p2),
          sfDataDefs = sfDataDefs p1 ++ sfDataDefs p2,
          sfMeasureDefs = sfMeasureDefs p1 ++ sfMeasureDefs p2}
    
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
  matches <- Glob.glob $ loadPath ++ "/**/" ++ moduleName ++ extension
  case uncons matches of
    Nothing -> fail $ "Could not locate module '" ++ moduleName ++ "'. Please check the specified search path."
    Just (file,_) -> return file


loadProgram :: Maybe FilePath -> Text -> Maybe Id -> IO (Program Positioned)
loadProgram pathSearch modName fn = do
  searchPathfromEnv <- lookupEnv "ATLAS_SEARCH"
  let path = (`fromMaybe` pathSearch) . (`fromMaybe` searchPathfromEnv) $ "."
  surfaceProg <- loadSurfaceProgram path modName

  let run step = either printSrcError return . step

  contextualizeProg
    . normalizeProg
    <$> (run inferProgram
         =<< run elabProgram surfaceProg)
