{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}

module Module where


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
import Ast
import StaticAnalysis(calledFunctions)
import qualified Parsing.Program(parseModule)
import qualified System.FilePath.Glob as Glob

import Data.Tree

extension = ".ml"

data LoaderState = LoaderState {
  dependents :: Map Fqn (Set Fqn), -- depedency fqdn -> [dependent fqdn]
  loadedDefinitions :: Map Fqn ParsedFunDef,
  processedDefinitions :: Set Fqn,
  todo :: [Fqn]
                               }

loadLazy :: FilePath -> Fqn -> IO (ParsedModule, Text)
loadLazy loadPath rootFqn = do
  let moduleName = fst rootFqn
  moduleFile <- findModule loadPath (T.unpack moduleName)
  contents <- TextIO.readFile moduleFile
  let parsedDefs = Parsing.Program.parseModule moduleFile moduleName contents
  parsedMod <- evalStateT (buildModule loadPath moduleName) $
    LoaderState
    M.empty
    (M.fromList $ zip (map (pfFqn . funAnn) parsedDefs) parsedDefs)
    S.empty
    [rootFqn]
  return (parsedMod, contents)

load :: FilePath -> Text -> IO (ParsedModule, Text)
load loadPath moduleName = do
  moduleFile <- findModule loadPath (T.unpack moduleName)
  contents <- TextIO.readFile moduleFile
  let parsedDefs = Parsing.Program.parseModule moduleFile moduleName contents
  parsedDefs <- Parsing.Program.parseModule moduleFile moduleName <$> TextIO.readFile moduleFile
  let defsWithFqn = M.fromList $ zip (map (pfFqn . funAnn) parsedDefs) parsedDefs
  parsedMod <- evalStateT (buildModule loadPath moduleName) $
    LoaderState
    M.empty
    defsWithFqn
    S.empty
    (M.keys defsWithFqn)
  return (parsedMod, contents)


buildModule :: FilePath -> Text -> StateT LoaderState IO ParsedModule
buildModule loadPath modName = do
  fqn@(moduleName, definitionName) <- popTodo
  def <- retrieveDefinition fqn
  addVertex fqn
  let dependencies = calledFunctions def moduleName
  addDependencyEdges fqn dependencies
  processed <- gets processedDefinitions
  pushTodos $ dependencies `S.difference` processed
  markAsProcessed fqn

  ifM someTodos (buildModule loadPath modName) (moduleFromLoaderState modName)

moduleFromLoaderState :: Text -> StateT LoaderState IO ParsedModule
moduleFromLoaderState modName = do
  LoaderState{..} <- get
  let edgeList = map (\(key, keys) -> (key, key, S.toList keys)) $ M.toList dependents
  let (g, vertexFqnMap, fqnVertexMap) = G.graphFromEdges edgeList
  let vertexFqnMap' = (\(fqn, _, _) -> fqn) . vertexFqnMap
  let depSccs = G.scc g
  return $ Module
           modName
           (sccsToRecBindings vertexFqnMap'  depSccs)
           (M.mapKeys snd loadedDefinitions)
  where sccsToRecBindings :: (G.Vertex -> Fqn) -> [Tree G.Vertex] -> [[Id]]
        sccsToRecBindings vertexFqnMap = map (map (snd . vertexFqnMap) . toList)

markAsProcessed :: Fqn -> StateT LoaderState IO ()
markAsProcessed fqn = modify (\s -> s {processedDefinitions = S.insert fqn (processedDefinitions s)})
  
someTodos :: StateT LoaderState IO Bool
someTodos = gets ((/=[]) . todo)
    
pushTodos :: Set Fqn -> StateT LoaderState IO ()
pushTodos fqns = modify (\s -> s {todo = todo s ++ S.toList fqns})

addVertex :: Fqn -> StateT LoaderState IO ()
addVertex fqn = modify (\s -> s {dependents = initVertex $ dependents s})
  where initVertex = M.insertWith (\new old -> old) fqn S.empty
  
addDependencyEdges :: Fqn -> Set Fqn -> StateT LoaderState IO ()
addDependencyEdges dependent dependencies =
  modify (\s -> s {dependents = insertsDepentent $ dependents s})
  where insertsDepentent m = S.foldr updateDependency m dependencies
        updateDependency = M.alter (Just . S.insert dependent . fromMaybe S.empty) 

retrieveDefinition :: Fqn -> StateT LoaderState IO ParsedFunDef
retrieveDefinition fqn@(mod, fun) = do
  found <- gets $ M.lookup fqn . loadedDefinitions
  liftIO $ case found of
    Just def -> return def
    Nothing -> fail $ "Could not find a definition for '" ++ (T.unpack fun) ++ "' in module '" ++ T.unpack mod ++ "'."
    

storeDefinitions :: [ParsedFunDef] -> StateT LoaderState IO ()
storeDefinitions defs = modify (\s -> s {loadedDefinitions = insertDefs s})
  where newDefs = M.fromList $ zip (map (pfFqn . funAnn) defs) defs
        insertDefs state = newDefs `M.union` loadedDefinitions state
  
popTodo :: StateT LoaderState IO Fqn
popTodo = do
  maybeTodos <- gets $ uncons . todo
  let (next, rest) = case maybeTodos of
        Nothing -> error "popTodo called on empty list."
        Just l -> l
  modify (\s -> s {todo = rest})
  return next

findModule :: String -> String -> IO FilePath
findModule loadPath moduleName = do
  matches <- Glob.glob $ loadPath ++ "/**/" ++ moduleName ++ extension
  case uncons matches of
    Nothing -> fail $ "Could not locate module '" ++ moduleName ++ "'. Please check the specified search path."
    Just (file,_) -> return file

