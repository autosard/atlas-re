{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Constants where

import Primitive(Id)
import Typing.Scheme
import Typing.Type(Type(TGen, TAp), Tycon(Tree, Bool, Prod, List, Num), fn)
import Ast(Val(ConstVal, LitVal), Literal(LitNum), Expr, pattern Const)
import qualified Data.Text as T

treeT = TAp Tree [TGen 0]
tupleT = TAp Prod [TGen 0, TGen 1]
boolT = TAp Bool []
numT = TAp Num []
listT = TAp List [TGen 0]

pattern TupleT :: Type -> Type -> Type
pattern TupleT x y <- TAp Prod [x, y]

treeSc = Forall 1 treeT
tupleSc = Forall 2 tupleT
boolSc = Forall 0 boolT

constType :: Id -> Scheme
constType "node" = Forall 1 $ [treeT, TGen 0, treeT] `fn` treeT
constType "leaf" = Forall 1 treeT
constType "nil" = Forall 1 listT
constType "cons" = Forall 1 $ [TGen 0, listT] `fn` listT
constType "(,)" = Forall 2 $ [TGen 0, TGen 1] `fn` tupleT
constType "true" = Forall 0 boolT
constType "false" = Forall 0 boolT
constType "numLit" = Forall 0 (TAp Num [])
constType "error" = Forall 1 (TGen 0)
constType "LT" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType "LE" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType "EQ" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType "GT" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
constType "+" = Forall 0 $ [numT, numT] `fn` numT
constType "-" = Forall 0 $ [numT, numT] `fn` numT
constType c = error $ "undefined constant '" ++ T.unpack c ++ "'"


constEval :: Id -> [Val] -> Val
constEval "node" args = ConstVal "node" args
constEval "leaf" args = ConstVal "leaf" args
constEval "nil" args = ConstVal "nil" args
constEval "cons" args = ConstVal "cons" args
constEval "(,)" args = ConstVal "(,)" args
constEval "true" args = ConstVal "true" args
constEval "false" args = ConstVal "false" args
constEval "error" args = ConstVal "error" args
constEval "LT" [x, y] = evalLT x y
constEval "EQ" [x, y] = evalEQ x y
constEval "GT" [x, y] = evalGT x y
constEval "+" [LitVal (LitNum x), LitVal (LitNum y)] = LitVal $ LitNum (x + y)
constEval "-" [LitVal (LitNum x), LitVal (LitNum y)] = LitVal $ LitNum (x - y)
constEval c _ = error $ "undefined constant '" ++ T.unpack c ++ "'"

-- basic consts do not change potential
isBasicConst :: Expr a -> Bool
isBasicConst (Const "EQ" _ ) = True
isBasicConst (Const "LT" _ ) = True
isBasicConst (Const "GT" _ ) = True
isBasicConst (Const "LE" _ ) = True
isBasicConst (Const "+" _ ) = True
isBasicConst (Const "-" _ ) = True
isBasicConst _ = False

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


