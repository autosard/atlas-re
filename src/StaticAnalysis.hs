{-# LANGUAGE OverloadedStrings #-}

module StaticAnalysis where

import Syntax.Ast
import Primitive(Id)
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

unionMap :: (Ord b) => (a -> Set b) -> [a] -> Set b
unionMap f xs = S.unions $ map f xs

calledFunctions' :: Expr a -> Set Id
calledFunctions' (App id exps) = S.insert id $ unionMap calledFunctions' exps
calledFunctions' (Ite e1 e2 e3) = unionMap calledFunctions' [e1, e2, e3]
calledFunctions' (Match e1 arms) = calledFunctions' e1 `S.union`
  unionMap (calledFunctions' . (\(MatchArm _ e) -> e)) arms
calledFunctions' (Let _ e1 e2) = unionMap calledFunctions' [e1, e2]
calledFunctions' (Tick _ e) = calledFunctions' e
calledFunctions' (Const _ args) = unionMap calledFunctions' args
calledFunctions' _ = S.empty

freeVars :: Expr a -> Set Id
freeVars (Var id) = S.singleton id
freeVars (Const _ exps) = unionMap freeVars exps
freeVars (Ite e1 e2 e3) = unionMap freeVars [e1, e2, e3]
freeVars (Match m arms) = freeVars m `S.union`
  unionMap (freeVars . (\(MatchArm _ e) -> e)) arms
freeVars (App _ exps) = unionMap freeVars exps
freeVars (Let id e1 e2) = S.delete id $ freeVars e1 `S.union` freeVars e2
freeVars (Tick _ e) = freeVars e
freeVars _ = S.empty

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

