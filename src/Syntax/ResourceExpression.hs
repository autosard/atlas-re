{-# LANGUAGE StrictData #-}

module Syntax.ResourceExpression where

import Primitive(Id, HasVars(..), Substitutable(..), PrettyPrint(..))
import qualified Data.Set as S
import Data.List (intercalate)
import qualified Data.Text as T
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet


import Syntax.ResourceExpression.Size

data ResourceTerm
  = RTSize Id
  | RTLog SizeSum
  | RTPhi Id
  | RTBinom SizeSum Int
  | RTProd (MultiSet ResourceTerm)
  | RTId
  -- special forms for specifing potential functions
  -- this is normalized away in templates
  | RTScale Rational ResourceTerm
  | RTCoeffScale Int ResourceTerm ResourceTerm
  deriving (Eq, Ord, Show)

isOne :: ResourceTerm -> Bool
isOne RTId = True
isOne other = False


instance Substitutable ResourceTerm where
  subst env (RTSize s) = RTSize $ subst env s
  subst env (RTProd bs) = RTProd $ MSet.map (subst env) bs
  subst env (RTLog ss) = RTLog $ subst env ss
  subst env (RTPhi x) = RTPhi $ subst env x
  subst env (RTBinom ss k) = RTBinom (subst env ss) k
  subst env RTId = RTId
  subst env (RTScale k t) = RTScale k $ subst env t
  subst env (RTCoeffScale i idx t) = RTCoeffScale i idx $ subst env t

instance HasVars ResourceTerm where
  freeVars (RTSize x) = S.singleton x
  freeVars (RTLog ss) = freeVars ss
  freeVars (RTBinom ss k) = freeVars ss 
  freeVars (RTPhi x) = S.singleton x
  freeVars (RTProd bs) = S.unions $ MSet.map freeVars bs
  freeVars (RTScale k t) = freeVars t
  freeVars (RTCoeffScale i idx t) = freeVars t
  freeVars RTId = S.empty

instance PrettyPrint ResourceTerm where
  prettyPrint (RTSize v) = "|" ++ T.unpack v ++ "|"
  prettyPrint (RTLog s) = "log(" ++ prettyPrint s ++ ")"
  prettyPrint (RTPhi v) = "phi(" ++ T.unpack v ++ ")"
  prettyPrint (RTBinom s k) = "binom(" ++ prettyPrint s ++ ", " ++ show k ++ ")"
  prettyPrint (RTProd ts) = intercalate " * " $ map prettyPrint (MSet.toList ts)
  prettyPrint RTId = "1"
  prettyPrint (RTScale q inner) = prettyPrint q ++ " * " ++ parenthesize inner
    where
      parenthesize t@RTProd{} = "(" ++ prettyPrint t ++ ")"
      parenthesize t           = prettyPrint t

isZero :: ResourceTerm -> Bool
isZero (RTLog s) = s == sizeConst 1
isZero otherTerm = False

isPotential (RTPhi _) = True
isPotential _ = False
