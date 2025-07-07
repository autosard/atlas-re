{-# LANGUAGE OverloadedStrings #-}

module StaticAnalysis where

import Ast
import Primitive(Id)
import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S
import Constants (isBasicConst)

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

-- isZeroCostExpr :: Expr a -> Bool
-- isZeroCostExpr (Var _) = True
-- isZeroCostExpr c@(Const _ exps) = isBasicConst c && all isZeroCostExpr exps
-- isZeroCostExpr (Ite e1 e2 e3) = isZeroCostExpr e1 && isZeroCostExpr e2 && isZeroCostExpr e3
-- isZeroCostExpr (Match m arms) = all (\(MatchArm _ e) -> isZeroCostExpr e) arms
-- isZeroCostExpr (Let _ e1 e2) = isZeroCostExpr e1 && isZeroCostExpr e2
-- isZeroCostExpr _ = False
