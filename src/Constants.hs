{-# LANGUAGE OverloadedStrings #-}
module Constants where

import Primitive(Id)
import Typing.Scheme
import Typing.Type(Type(TGen, TAp), Tycon(Tree, Bool, Prod), fn)
import Ast(Val(ConstVal, LitVal), Literal(LitNum))
import qualified Data.Text as T

treeT = TAp Tree [TGen 0]
tupleT = TAp Prod [TGen 0, TGen 1]
boolT = TAp Bool []

treeSc = Forall 1 treeT
tupleSc = Forall 2 tupleT
boolSc = Forall 0 boolT

constType :: Id -> Scheme
constType "node" = Forall 1 $ [treeT, TGen 0, treeT] `fn` treeT
constType "leaf" = Forall 1 treeT
constType "(,)" = Forall 2 $ [TGen 0, TGen 1] `fn` tupleT
constType "true" = Forall 0 boolT
constType "false" = Forall 0 boolT
constType "LT" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType "EQ" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType "GT" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType c = error $ "undefined constant '" ++ T.unpack c ++ "'"


constEval :: Id -> [Val] -> Val
constEval "node" args = ConstVal "node" args
constEval "leaf" args = ConstVal "leaf" args
constEval "(,)" args = ConstVal "(,)" args
constEval "true" args = ConstVal "true" args
constEval "false" args = ConstVal "false" args
constEval "LT" [x, y] = evalLT x y
constEval "EQ" [x, y] = evalEQ x y
constEval "GT" [x, y] = evalGT x y
constEval c _ = error $ "undefined constant '" ++ T.unpack c ++ "'"

toBool :: Bool -> Val
toBool True = ConstVal "true" []
toBool False = ConstVal "false" []

evalLT :: Val -> Val -> Val
evalLT (LitVal (LitNum x)) (LitVal (LitNum y)) = toBool $ x < y
evalLT _ _ = error "LT is only implemented for numbers."

evalEQ :: Val -> Val -> Val
evalEQ (LitVal (LitNum x)) (LitVal (LitNum y)) = toBool $ x == y
evalEQ _ _ = error "EQ is only implemented for numbers."

evalGT :: Val -> Val -> Val
evalGT (LitVal (LitNum x)) (LitVal (LitNum y)) = toBool $ x > y
evalGT _ _ = error "GT is only implemented for numbers."


