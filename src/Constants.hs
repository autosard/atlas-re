{-# LANGUAGE OverloadedStrings #-}
module Constants where

import Primitive(Id)
import Typing.Scheme
import Typing.Type(Type(TGen, TAp), Tycon(Tree, Bool, Prod), fn)
import qualified Data.Text as T

--treeT = Forall 1 (TAp Tree [TGen 0])
--tupleT = Forall 2 (TAp Prod [TGen 0, TGen 1])
--boolT = Forall 0 (TAp Bool [])

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
