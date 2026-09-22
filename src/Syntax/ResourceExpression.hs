{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}

module Syntax.ResourceExpression
  ( ResourceTerm (..)
  , SizeTerm (..)
  , ResourceExpr
  , fromSizeExpr
  , RScalar (..)
  , SizeExpr
  , isZero
  , isOne
  , isPotential
  ) where

import qualified Data.Set as S
import Data.List (intercalate)
import qualified Data.Text as T
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet

import Syntax
  ( Id
  , HasVars(..)
  , Substitutable (..)
  , HasProduct (..)
  , normalisedProd)
import Syntax.PrettyPrint (PrettyPrint(..))
import qualified Syntax.FreeModule as FM
import Syntax.FreeModule (FreeModule)

data SizeTerm = SVar Id | SId
  deriving (Eq, Ord, Show)

type SizeExpr = FreeModule SizeTerm Rational

data ResourceTerm
  = RTSize Id
  | RTLog SizeExpr
  | RTPhi Id
  | RTBinom SizeExpr Int
  | RTProd (MultiSet ResourceTerm)
  | RTId 
  deriving (Eq, Ord, Show)

data RScalar =
  RSConst Rational
  | RSCoeff Int ResourceTerm
  | RSAdd RScalar RScalar
  | RSMul RScalar RScalar
  deriving (Eq, Ord, Show)

instance Num RScalar where
  (+) (RSConst r1) (RSConst r2) = RSConst (r1 + r2)
  (+) s1 s2 = RSAdd s1 s2
  (*) (RSConst r1) (RSConst r2) = RSConst (r1 * r2)
  (*) s1 s2 = RSMul s1 s2
  negate (RSConst r) = RSConst (-r)
  negate s = RSMul (RSConst (-1)) s
  fromInteger = RSConst . fromIntegral
  abs (RSConst k) = RSConst (abs k)
  abs q@(RSCoeff _ _) = q
  

type ResourceExpr = FreeModule ResourceTerm RScalar

fromSizeExpr :: SizeExpr -> ResourceExpr
fromSizeExpr = FM.bimap fromSizeTerm RSConst
  
fromSizeTerm :: SizeTerm -> ResourceTerm
fromSizeTerm (SVar x) = RTSize x
fromSizeTerm SId = RTId

instance HasProduct ResourceTerm where
  one = RTId
  prod = RTProd
  unprod (RTProd ts) = Just ts
  unprod otherTerm   = Nothing 

instance Semigroup ResourceTerm where
  (<>) = normalisedProd

instance Monoid ResourceTerm where
  mempty = RTId

instance HasVars SizeTerm where
  freeVars (SVar x) = S.singleton x
  freeVars SId = S.empty
  
instance Substitutable SizeTerm where
  subst env (SVar x) = SVar $ subst env x
  subst env SId = SId

instance Substitutable SizeExpr where
  subst env = FM.map (subst env)

instance Substitutable ResourceTerm where
  subst env (RTSize s) = RTSize $ subst env s
  subst env (RTProd bs) = RTProd $ MSet.map (subst env) bs
  subst env (RTLog ss) = RTLog $ subst env ss
  subst env (RTPhi x) = RTPhi $ subst env x
  subst env (RTBinom ss k) = RTBinom (subst env ss) k
  subst env RTId = RTId

instance Substitutable ResourceExpr where
  subst env = FM.map (subst env)

instance HasVars ResourceTerm where
  freeVars (RTSize x) = S.singleton x
  freeVars (RTLog ss) = freeVars ss
  freeVars (RTBinom ss k) = freeVars ss 
  freeVars (RTPhi x) = S.singleton x
  freeVars (RTProd bs) = S.unions $ MSet.map freeVars bs
  freeVars RTId = S.empty

instance PrettyPrint SizeTerm where
  prettyPrint (SVar v) = "|" ++ T.unpack v ++ "|"
  prettyPrint SId = "1"

instance PrettyPrint ResourceTerm where
  prettyPrint (RTSize v) = "|" ++ T.unpack v ++ "|"
  prettyPrint (RTLog s) = "log(" ++ prettyPrint s ++ ")"
  prettyPrint (RTPhi v) = "phi(" ++ T.unpack v ++ ")"
  prettyPrint (RTBinom s k) = "binom(" ++ prettyPrint s ++ ", " ++ show k ++ ")"
  prettyPrint (RTProd ts) = intercalate " * " $ map prettyPrint (MSet.toList ts)
  prettyPrint RTId = "1"



isZero :: ResourceTerm -> Bool
isZero (RTLog s) = s == FM.singleton SId
isZero otherTerm = False

isPotential (RTPhi _) = True
isPotential _ = False

isOne :: ResourceTerm -> Bool
isOne RTId = True
isOne other = False


