{-# LANGUAGE StrictData #-}

module Syntax.ResourceExpression where

import Primitive(Id, HasVars(..), Substitutable(..), PrettyPrint(..))
import Data.Bifunctor (Bifunctor(first))
import qualified Data.Set as S
import Data.Set (Set)
import Data.List (intercalate)
import qualified Data.Text as T


import Syntax.ResourceExpression.Size

-- instance Substitutable SizeAtom where
--   subst env (SVar x) = SVar (subst env x)
--   subst env (SConst c) = SConst c

data ResourceTerm
  = RTSize Id
  | RTBinoms [(SizeSum, Int)]
  | RTLog SizeSum
  | RTPhi Id
  | RTId 
  -- special form for specifing potential functions
  -- this is normalized aways in templates
  | RTScale Rational ResourceTerm
  deriving (Eq, Ord, Show)

instance Substitutable ResourceTerm where
  subst env (RTSize s) = RTSize $ subst env s
  subst env (RTBinoms bs) = RTBinoms $ map (first (subst env)) bs
  subst env (RTLog ss) = RTLog $ subst env ss
  subst env (RTPhi x) = RTPhi $ subst env x
  subst env RTId = RTId
  subst env (RTScale k t) = RTScale k $ subst env t

instance HasVars ResourceTerm where
  freeVars (RTSize x) = S.singleton x
  freeVars (RTBinoms bs) = S.unions $ map (freeVars . fst) bs
  freeVars (RTLog ss) = freeVars ss
  freeVars (RTPhi x) = S.singleton x
  freeVars RTId = S.empty

instance PrettyPrint ResourceTerm where
  prettyPrint (RTSize v) = "|" ++ T.unpack v ++ "|"
  prettyPrint (RTBinoms binoms) = intercalate " * " [ prettyBinom s k | (s, k) <- binoms ]
    where
      prettyBinom s k = "binom(" ++ prettyPrint s ++ ", " ++ show k ++ ")"
  prettyPrint (RTLog s) = "log(" ++ prettyPrint s ++ ")"
  prettyPrint (RTPhi v) = "phi(" ++ T.unpack v ++ ")"
  prettyPrint RTId = "1"
  prettyPrint (RTScale q inner) = prettyPrint q ++ " * " ++ parenthesize inner
    where
      parenthesize t@RTBinoms{} = "(" ++ prettyPrint t ++ ")"
      parenthesize t           = prettyPrint t
