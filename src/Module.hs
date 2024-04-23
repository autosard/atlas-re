{-# LANGUAGE RecordWildCards #-}

module Module where

import qualified Data.Graph as G
import Data.Graph(Graph)
import qualified Data.Set as S
import Data.Set(Set)
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Text.IO as TextIO(readFile)
import qualified Data.Text as T
import Data.Text(Text)
import Data.List(uncons)
import Data.Maybe(fromMaybe)

import System.FilePath(FilePath)

import Control.Monad.State
import Control.Monad.Extra

import Ast(ParsedFunDef , Fqn, funAnn, pfFqn)
import StaticAnalysis(calledFunctions)
import qualified Parser(run)
import qualified System.FilePath.Glob as Glob

import Data.Tree

extension = ".ml"

data Program = Program {
  progFunDefs :: Map Fqn ParsedFunDef,
  progRoots :: [Fqn],
  progCallGraphSCC :: [G.Tree G.Vertex],
  progVertexFqnMap :: G.Vertex -> (Fqn, Fqn, [Fqn]),
  progFqnVertexMap :: Fqn -> Maybe G.Vertex
  }

data LoaderState = LoaderState {
  roots :: [Fqn],
  dependents :: Map Fqn (Set Fqn), -- depedency fqdn -> [dependent fqdn]
  loadedDefinitions :: Map Fqn ParsedFunDef,
  loadedModules :: Set Text,
  processedDefinitions :: Set Fqn,
  todo :: [Fqn]
                               }

load :: FilePath -> [Fqn] -> IO Program
load loadPath rootFqns = do
  evalStateT (buildProgram loadPath) $ LoaderState rootFqns M.empty M.empty S.empty S.empty rootFqns


buildProgram :: FilePath -> StateT LoaderState IO Program
buildProgram loadPath = do
  fqn@(moduleName, definitionName) <- popTodo

  loaded <- isLoaded moduleName
  unless loaded (
    do
      moduleFile <- liftIO $ findModule loadPath (T.unpack moduleName)
      parsedModule <- liftIO (Parser.run moduleFile moduleName <$> TextIO.readFile moduleFile)
      storeDefinitions parsedModule
      markAsLoaded moduleName
    )

  def <- retrieveDefinition fqn
  addVertex fqn
  let dependencies = calledFunctions def moduleName
  addDependencyEdges fqn dependencies
  loaded <- gets processedDefinitions
  pushTodos $ dependencies `S.difference` loaded
  markAsProcessed fqn

  ifM someTodos (buildProgram loadPath) programFromLoaderState

programFromLoaderState :: StateT LoaderState IO Program
programFromLoaderState = do
  LoaderState{..} <- get
  let progFunDefs = loadedDefinitions
  let progRoots = roots
  let edgeList = map (\(key, keys) -> (key, key, S.toList keys)) $ M.toList dependents
  let (g, progVertexFqnMap, progFqnVertexMap)
        = G.graphFromEdges edgeList
  let progCallGraphSCC = G.scc g
  return Program{..}

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

isLoaded :: Text -> StateT LoaderState IO Bool
isLoaded mod = gets $ S.member mod . loadedModules

markAsLoaded :: Text -> StateT LoaderState IO ()
markAsLoaded mod = modify (\s -> s {loadedModules = S.insert mod (loadedModules s)})
  
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


prettyPrintSCC :: Program -> String
prettyPrintSCC Program{..} = foldr op "" progCallGraphSCC 
  where op tree [] = treeToString tree
        op tree string = string ++ ", " ++ treeToString tree
        treeToString G.Node{..} = show (((\(fqn, _, _) -> fqn) . progVertexFqnMap) rootLabel)
          ++ " -> [" ++ concatMap treeToString subForest ++ "]"
  


  


 
  
