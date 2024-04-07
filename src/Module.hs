module Module where

import qualified Data.Graph as G
import Data.Graph(Graph)
import qualified Data.Set as S
import Data.Set(Set)
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Text.IO as T(readFile)
import Data.List(uncons)

import System.FilePath(FilePath)

import Control.Monad.State


import Ast(FunctionDefinition)
import qualified Parser(run)
import qualified System.FilePath.Glob as Glob

extension = ".ml"

type Module = [FunctionDefinition]
type Fqn = (String, String)

data Program = Program {
  progFunDefs :: Map String FunctionDefinition,
  progRoots :: Set String,
  reverseDependencies :: Graph 
  }

data LoaderState = LoaderState {
  definitionCount :: Int,
  dependents :: Map String [String], -- depedency fqdn -> [dependent fqdn]
  loadedDefinitions :: Set String,
  todo :: [Fqn]
                               }


load :: FilePath -> [Fqn] -> IO String
load loadPath rootFqns = do
  evalStateT (buildProgram loadPath) $ LoaderState 0 M.empty S.empty rootFqns


buildProgram :: FilePath -> StateT LoaderState IO String
buildProgram loadPath = do
  (moduleName, definitionName) <- popTodo
  moduleFile <- liftIO $ findModule loadPath moduleName
  parsedModule <- liftIO (Parser.run moduleFile <$> T.readFile moduleFile)
  return $ show parsedModule

  
popTodo :: StateT LoaderState IO Fqn
popTodo = do
  state <- get
  let (next:todos) = todo state
  put state {todo = todos}
  return next

findModule :: String -> String -> IO FilePath
findModule loadPath moduleName = do
  matches <- Glob.glob $ loadPath ++ "/**/" ++ moduleName ++ extension
  case uncons matches of
    Nothing -> fail $ "Could not locate module '" ++ moduleName ++ "'. Please check the specified search path."
    Just (file,_) -> return file



  


  


 
  
