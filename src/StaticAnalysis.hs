{-# LANGUAGE OverloadedStrings #-}

module StaticAnalysis where

import Ast
import Primitive(Id)
import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S

resolveFunId :: Text -> Id -> Fqn
resolveFunId currentModule identifier = case suffix of
  "" -> (currentModule, prefix)
  _suffix -> (prefix, suffix)
  where (prefix, suffix) = T.break (== '.') identifier

calledFunctions :: FunDef a -> Text -> Set Fqn
calledFunctions (Fn _ _ body) moduleName =
  S.map (resolveFunId moduleName) $ calledFunctions' body

unionMap :: (Ord b) => (a -> Set b) -> [a] -> Set b
unionMap f xs = S.unions $ map f xs

calledFunctions' :: Expr a -> Set Id
calledFunctions' (App id exps) = S.insert id $ unionMap calledFunctions' exps
calledFunctions' (Ite e1 e2 e3) = unionMap calledFunctions' [e1, e2, e3]
calledFunctions' (Match e1 arms) = calledFunctions' e1 `S.union` unionMap (calledFunctions' . snd) arms
calledFunctions' (BExpr _ e1 e2) = unionMap calledFunctions' [e1, e2]
calledFunctions' (Let _ e1 e2) = unionMap calledFunctions' [e1, e2]
calledFunctions' (Tick _ e) = calledFunctions' e
calledFunctions' (Const _ args) = unionMap calledFunctions' args
calledFunctions' _ = S.empty
