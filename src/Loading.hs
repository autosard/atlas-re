{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}

module Loading where


import qualified Data.Graph as G
import qualified Data.Set as S
import Data.Set(Set)
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Text.IO as TextIO(readFile)
import qualified Data.Text as T
import Data.Text(Text)
import Data.List(uncons)
import Data.Maybe(fromMaybe)
import Data.Foldable(toList)

import Control.Monad.State
import Control.Monad.Extra

import Primitive(Id)
import Syntax.Ast
import StaticAnalysis(calledFunctions)
import Parsing.Program(parseProgram)
import qualified System.FilePath.Glob as Glob

import Data.Tree
import Control.Monad.Extra (concatMapM)

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
          sfConfig = sfConfig p1,
          sfFunDefs = M.union (sfFunDefs p1) (sfFunDefs p2),
          sfDataDefs = sfDataDefs p1 ++ sfDataDefs p2,
          sfMeasureDefs = sfMeasureDefs p1 ++ sfMeasureDefs p2}
    
loadProgram :: FilePath -> Text -> IO SurfaceProgram
loadProgram loadPath initialMod = evalStateT go (LoaderState M.empty)
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

-- moduleFromLoaderState :: Text -> ModConfig -> StateT LoaderState IO ParsedModule
-- moduleFromLoaderState modName config = do
--   LoaderState{..} <- get
--   let edgeList = map (\(key, keys) -> (key, key, S.toList keys)) $ M.toList dependents
--   let (g, vertexFqnMap, fqnVertexMap) = G.graphFromEdges edgeList
--   let vertexFqnMap' = (\(fqn, _, _) -> fqn) . vertexFqnMap
--   let depSccs = G.scc g
--   return $ Module
--            modName
--            config
--            (reverse (sccsToRecBindings vertexFqnMap'  depSccs))
--            (M.mapKeys snd loadedDefinitions)
--   where sccsToRecBindings :: (G.Vertex -> Fqn) -> [Tree G.Vertex] -> [[Id]]
--         sccsToRecBindings vertexFqnMap = map (map (snd . vertexFqnMap) . toList)

-- markAsProcessed :: Fqn -> StateT LoaderState IO ()
-- markAsProcessed fqn = modify (\s -> s {processedDefinitions = S.insert fqn (processedDefinitions s)})
  
-- someTodos :: StateT LoaderState IO Bool
-- someTodos = gets ((/=[]) . todo)
    
-- pushTodos :: Set Fqn -> StateT LoaderState IO ()
-- pushTodos fqns = modify (\s -> s {todo = todo s ++ S.toList fqns})

-- addVertex :: Fqn -> StateT LoaderState IO ()
-- addVertex fqn = modify (\s -> s {dependents = initVertex $ dependents s})
--   where initVertex = M.insertWith (\new old -> old) fqn S.empty
  
-- addDependencyEdges :: Fqn -> Set Fqn -> StateT LoaderState IO ()
-- addDependencyEdges dependent dependencies =
--   modify (\s -> s {dependents = insertsDepentent $ dependents s})
--   where insertsDepentent m = S.foldr updateDependency m dependencies
--         updateDependency = M.alter (Just . S.insert dependent . fromMaybe S.empty) 

-- retrieveDefinition :: Fqn -> StateT LoaderState IO ParsedFunDef
-- retrieveDefinition fqn@(mod, fun) = do
--   found <- gets $ M.lookup fqn . loadedDefinitions
--   liftIO $ case found of
--     Just def -> return def
--     Nothing -> fail $ "Could not find a definition for '" ++ (T.unpack fun) ++ "' in module '" ++ T.unpack mod ++ "'."
    

-- storeDefinitions :: [ParsedFunDef] -> StateT LoaderState IO ()
-- storeDefinitions defs = modify (\s -> s {loadedDefinitions = insertDefs s})
--   where newDefs = M.fromList $ zip (map (pfFqn . funAnn) defs) defs
--         insertDefs state = newDefs `M.union` loadedDefinitions state
  
-- popTodo :: StateT LoaderState IO Fqn
-- popTodo = do
--   maybeTodos <- gets $ uncons . todo
--   let (next, rest) = case maybeTodos of
--         Nothing -> error "popTodo called on empty list."
--         Just l -> l
--   modify (\s -> s {todo = rest})
--   return next

findModule :: String -> String -> IO FilePath
findModule loadPath moduleName = do
  matches <- Glob.glob $ loadPath ++ "/**/" ++ moduleName ++ extension
  case uncons matches of
    Nothing -> fail $ "Could not locate module '" ++ moduleName ++ "'. Please check the specified search path."
    Just (file,_) -> return file

-- addTypeSig :: Id -> StateT LoaderState IO ()
-- addTypeSig fn sig = do
--   st <- gets loadedSig
--   let ts = typeSig st

--   when (M.member i ts) $
--     error ("duplicate type signature for " ++ show i)

--   let ts' = M.insert i sig ts

--   modify $ \s ->
--     s { loadedSig = st { typeSig = ts' } }
