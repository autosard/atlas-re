{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn
import Ast

import Data.Set(Set)
import Data.List(intercalate)
import qualified Data.Set as S
import Lens.Micro.Platform
import Data.Text(unpack)

data WeakenArg = Mono | L2xy
  deriving (Eq, Ord, Show)

data Rule 
  = Const
  | Cmp
  | Var
  | Ite 
  | Match 
  | Let 
  | App 
  | TickNow 
  | TickDefer
  | WeakenVar
  | Weaken [WeakenArg]
  | Shift
  deriving(Eq, Show)

data RuleApp
  = ExprRuleApp Rule Bool RsrcAnn RsrcAnn [Constraint] TypedExpr
  | FunRuleApp TypedFunDef
  | ProgRuleApp TypedModule

printRuleApp :: Set Constraint -> RuleApp -> String
printRuleApp unsatCore (ExprRuleApp rule cf q q' cs e) = show rule ++ printCf ++ printAnns ++": " ++ printExprHead e ++ printCs (unsat cs)  
  where printAnns = " [" ++ printQ q ++ " |- " ++ printQ q' ++ "]"
        printCs cs = "\n\t" ++ intercalate ",\n\t" (S.toList cs) 
        unsat cs = S.map printConstraint (S.fromList cs `S.intersection` unsatCore)
        printQ q = "q" ++ show (q^.annId) 
        printCf = if cf then " (cf)" else ""
printRuleApp _ (FunRuleApp (Fn name _ _)) = "Fun: " ++ unpack name
printRuleApp _ (ProgRuleApp _) = "Prog" 

