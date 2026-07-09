{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax.Constants where

import Primitive(Id)
import Typing.Scheme
import Typing.Type
import Syntax.Ast
import qualified Data.Text as T
import Data.Maybe (isJust)
import Data.Map as M


builtInDataDefs :: DataEnv
builtInDataDefs = M.fromList
  [("()", DataInfo {
       diParams=[],
       diCtors=[
           CtorInfo {
               ciName = "()",
               ciType = Forall 0 (TAp "()" [])
           }]
       }
   ),
   ("(,)", DataInfo {
       diParams=["a","b"],
       diCtors=[
           CtorInfo {
               ciName = "(,)",
               ciType = Forall 2 $
                 TFun (TGen 0) $
                 TFun (TGen 1) $
                 TAp "(,)" [TGen 0, TGen 1]
           }]
       }
   ),
   ("Nat", DataInfo {
       diParams=[],
       diCtors=[
           CtorInfo {
               ciName = "zero",
               ciType = Forall 0 (TAp "Nat" [])
           },
           CtorInfo {
               ciName = "suc",
               ciType = Forall 0 (TFun (TAp "Nat" []) (TAp "Nat" []))
           }]
       }
   ),
   ("Bool", DataInfo {
       diParams=[],
       diCtors=[
           CtorInfo {
               ciName = "true",
               ciType = Forall 0 (TAp "Bool" [])
           },
           CtorInfo {
               ciName = "false",
               ciType = Forall 0 (TAp "Bool" [])
           }]
       }
   )]

tNat = TAp "Nat" []

builtInFunTypes :: Map Id Scheme
builtInFunTypes = M.fromList
  [
    ("error", Forall 1 $ [TAp "String" []] `fn` TGen 0)
  , ("+", Forall 0 $ [tNat, tNat] `fn` tNat)
  , ("*", Forall 0 $ [tNat, tNat] `fn` tNat)
  , ("<=", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , (">=", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , ("<", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , (">", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , ("==", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  ]



--pattern TupleT :: Type -> Type -> Type
--pattern TupleT x y <- TAp Prod [x, y]

-- treeSc = Forall 1 treeT
-- tupleSc = Forall 2 tupleT
-- boolSc = Forall 0 boolT

-- constType :: Id -> Scheme
-- constType "node" = Forall 1 $ [treeT, TGen 0, treeT] `fn` treeT
-- constType "leaf" = Forall 1 treeT
-- constType "nil" = Forall 1 listT
-- constType "cons" = Forall 1 $ [TGen 0, listT] `fn` listT
-- constType "(,)" = Forall 2 $ [TGen 0, TGen 1] `fn` tupleT
-- constType "true" = Forall 0 boolT
-- constType "false" = Forall 0 boolT
-- constType "numLit" = Forall 0 (TAp Num [])
-- constType "error" = Forall 1 (TGen 0)
-- constType "weight" = Forall 1 $ [treeT] `fn` numT
-- constType "rank" = Forall 1 $ [treeT] `fn` numT
-- constType "LT" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
-- constType "LE" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
-- constType "EQ" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
-- constType "GT" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
-- constType "GE" = Forall 1 $ [TGen 0, TGen 0] `fn` boolT
-- constType "+" = Forall 0 $ [numT, numT] `fn` numT
-- constType "-" = Forall 0 $ [numT, numT] `fn` numT
-- constType c = if isNumConst c
--   then Forall 0 numT
--   else error $ "undefined constant '" ++ T.unpack c ++ "'"

-- evalConst :: Id -> [Val] -> Val
-- evalConst "LT" [x, y] = evalLT x y
-- evalConst "LE" [x, y] = evalLE x y
-- evalConst "EQ" [x, y] = evalEQ x y
-- evalConst "GT" [x, y] = evalGT x y
-- evalConst "+" [NumVal x, NumVal y] = NumVal (x + y)
-- evalConst "-" [NumVal x, NumVal y] = NumVal (x - y)
-- evalConst c _ = case T.stripPrefix "num#" c of
--   Just t -> if T.isPrefixOf "-" t
--     then NumVal $ - toInt (T.tail t)
--     else NumVal (toInt t)
--   Nothing -> error $ "undefined constant '" ++ T.unpack c ++ "'"
--   where toInt :: T.Text -> Int
--         toInt t = case decimal t of
--           Left e -> error e
--           Right (n, _) -> n


isNumConst :: T.Text -> Bool
isNumConst c = isJust $ T.stripPrefix "num#" c 

-- basic consts do not change potential
isBasicConst :: Expr a -> Bool
isBasicConst (Const "EQ" _ ) = True
isBasicConst (Const "LT" _ ) = True
isBasicConst (Const "GT" _ ) = True
isBasicConst (Const "LE" _ ) = True
isBasicConst (Const "GE" _ ) = True
isBasicConst (Const "+" _ ) = True
isBasicConst (Const "-" _ ) = True
isBasicConst (Const "true" _) = True
isBasicConst (Const "false" _) = True
isBasicConst (Const "weight" _) = True
isBasicConst (Const "rank" _) = True
isBasicConst (Const c _) | isNumConst c = True
isBasicConst _ = False

-- toBool :: Bool -> Val
-- toBool True = ConstVal "true" []
-- toBool False = ConstVal "false" []

-- evalLT :: Val -> Val -> Val
-- evalLT (NumVal x) (NumVal y) = toBool $ x < y
-- evalLT _ _ = error "LT is only implemented for numbers."

-- evalLE :: Val -> Val -> Val
-- evalLE (NumVal x) (NumVal y) = toBool $ x <= y
-- evalLE _ _ = error "LE is only implemented for numbers."

-- evalEQ :: Val -> Val -> Val
-- evalEQ (NumVal x) (NumVal y) = toBool $ x == y
-- evalEQ _ _ = error "EQ is only implemented for numbers."

-- evalGT :: Val -> Val -> Val
-- evalGT (NumVal x) (NumVal y) = toBool $ x > y
-- evalGT _ _ = error "GT is only implemented for numbers."
