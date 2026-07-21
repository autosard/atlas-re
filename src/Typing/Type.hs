{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Typing.Type where

import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M


import Primitive(Id, PrettyPrint(..))
import Data.Maybe (isJust)
import Control.Monad (zipWithM, foldM)

data Type
  = TVar Id
  | TAp Id [Type]
  | TFun Type Type
  | TGen Int
  deriving (Eq, Ord, Show)


prod :: [Type] -> Type
prod [] = error "empty product"
prod [t] = t
prod [t1,t2] = TAp "(,)" [t1, t2]
prod (t:ts) = TAp "(,)" [t, prod ts]

unprod :: Type -> [Type]
unprod (TAp "(,)" [t1, t2]) = t1 : unprod t2
unprod t = [t]

tCurry :: [Type] -> Type -> Type
tCurry args result = foldr TFun result args

fn :: [Type] -> Type -> Type
fn [] to = to
fn from to = TFun (prod from) to

instance PrettyPrint Type where
  prettyPrint = runPrec 0 
    where
      -- d represents the current precedence depth
      runPrec :: Int -> Type -> String
      runPrec _ (TVar x)  = T.unpack x
      runPrec _ (TGen n)  = "?" ++ show n
    
      -- Type application (e.g., Tree a) has higher precedence (tier 1)
      runPrec d (TAp c [])   = T.unpack c
      runPrec d (TAp c args) = parensIf (d > 0) $ 
        T.unpack c ++ " " ++ unwords (map (runPrec 1) args)
    
      -- Function arrow is right-associative and has lower precedence (tier 0)
      runPrec d (TFun arg res) = parensIf (d > 0) $
        runPrec 1 arg ++ " -> " ++ runPrec 0 res

      -- Helper to conditionally wrap strings in parentheses
      parensIf :: Bool -> String -> String
      parensIf True  s = "(" ++ s ++ ")"
      parensIf False s = s

isResourceRelevant :: Type -> Bool
isResourceRelevant (TAp c args) = True
isResourceRelevant (TVar _) = False
isResourceRelevant (TGen _) = False
isResourceRelevant (TFun _ _) = error "should not happen"


-- no proper unification just top level check
-- matchesType :: Type -> Type -> Bool
-- matchesType (TAp c1 _) (TAp c2 _) | c1 == c2 = True
-- matchesType _ _ = False

matchesTypes :: Type -> [Type] -> Bool
matchesTypes t = any (isJust . match t)

type SchemeSubst = Map Int Type

match :: Type -> Type -> Maybe SchemeSubst
match (TGen i) t = Just (M.singleton i t)
match (TVar u) (TVar v) 
  | u == v    = Just M.empty
  | otherwise = Nothing
match (TFun l1 r1) (TFun l2 r2) = do
  sl <- match l1 l2
  sr <- match r1 r2
  mergeSubst sl sr
match (TAp c1 tsl) (TAp c2 tsr)
  | c1 == c2 && length tsl == length tsr = do
      substs <- zipWithM match tsl tsr
      foldM mergeSubst M.empty substs
  | otherwise = Nothing
match _ _ = Nothing


mergeSubst :: SchemeSubst -> SchemeSubst -> Maybe SchemeSubst
mergeSubst s1 s2 =
  let conflicts = M.intersectionWith (==) s1 s2
  in if and conflicts 
     then Just (M.union s1 s2) 
     else Nothing
