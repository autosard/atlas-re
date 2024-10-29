{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn
import Ast

import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List(intercalate)

import Lens.Micro.Platform
import Data.Text(unpack)


data WeakenArg = Mono | L2xy | Neg
  deriving (Eq, Ord, Show)

data LetArg = NegE
  deriving (Eq, Ord, Show)

data Rule 
  = Const
  | Cmp
  | Var
  | Ite 
  | Match 
  | Let [LetArg]
  | App 
  | TickNow 
  | TickDefer
  | WeakenVar
  | Weaken [WeakenArg]
  | Shift
  deriving(Eq, Show)

data RuleApp
  = ExprRuleApp Rule Bool AnnCtx AnnCtx [Constraint] PositionedExpr
  | FunRuleApp PositionedFunDef
  | ProgRuleApp PositionedModule

printRuleApp :: Bool -> Maybe (Set Constraint, String -> String) -> RuleApp -> String
printRuleApp showCs integrateCore (ExprRuleApp rule cf q q' cs e) =
  case integrateCore of
    Just (unsatCore, highlight) ->
      let unsatCs = unsat cs unsatCore
          highlight' = if not . null $ unsatCs then highlight else id in
        highlight' printRule ++ printCs unsatCs 
    Nothing -> printRule ++ printCs cs
  where printRule = show rule ++ printCf ++ printAnns ++": " ++ printExprHead e ++ " (" ++ printPos srcPos ++ ")"
        printAnns = " [" ++ printMix q ++ " |- " ++ printMix q' ++ "]"
        printCs cs = if showCs then
          "\n\t" ++ intercalate ",\n\t" (map printConstraint cs)
          else ""
        unsat cs core = S.toList (S.fromList cs `S.intersection` core)
        printQ (t, q) = intercalate "," (map unpack (q^.args)) ++ " : " ++ "q" ++ show (q^.annId) ++ "|" ++ show t
        printMix ctx = intercalate "," $ map printQ (M.assocs ctx)
        printCf = if cf then " (cf)" else ""
        srcPos = case peSrc $ getAnn e of
          Loc pos -> pos
          DerivedFrom pos -> pos
          
printRuleApp _ _ (FunRuleApp (Fn name _ _)) = "Fun: " ++ unpack name
printRuleApp _ _ (ProgRuleApp _) = "Prog" 
