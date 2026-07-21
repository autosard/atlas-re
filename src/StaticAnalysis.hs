{-# LANGUAGE OverloadedStrings #-}

module StaticAnalysis where

import Syntax.Ast
import Primitive(Id, unionMap)
import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S
import Lens.Micro.Platform
import Data.Graph (stronglyConnComp, SCC(..))

resolveFunId :: Text -> Id -> Fqn
resolveFunId currentModule identifier = case suffix of
  "" -> (currentModule, prefix)
  _suffix -> (prefix, suffix)
  where (prefix, suffix) = T.break (== '.') identifier

calledFunctions :: FunDef a -> [Id]
calledFunctions fun = S.toList $ calledFunctions' (fun^.funBody)


calledFunctions' :: Expr a -> Set Id
calledFunctions' (App id exps) = S.insert id $ unionMap calledFunctions' exps
calledFunctions' (Ite e1 e2 e3) = unionMap calledFunctions' [e1, e2, e3]
calledFunctions' (Match e1 arms) = calledFunctions' e1 `S.union`
  unionMap (calledFunctions' . (\(MatchArm _ e) -> e)) arms
calledFunctions' (Let _ e1 e2) = unionMap calledFunctions' [e1, e2]
calledFunctions' (Tick _ e) = calledFunctions' e
calledFunctions' (Const _ args) = unionMap calledFunctions' args
calledFunctions' _ = S.empty


--------------------------------------------------------------------------------
-- Mutually Recursive Groups
-------------------------------------------------------------------------------

groupFuns :: [FunDef Elaborated] -> [[Id]]
groupFuns defs = map getGroup sccs
  where
    graphEdges = [ (def, _funName def, calledFunctions def) 
                 | def <- defs 
                 ]
    sccs = stronglyConnComp graphEdges
    getGroup (AcyclicSCC def) = [_funName def]
    getGroup (CyclicSCC defs') = map _funName defs'

