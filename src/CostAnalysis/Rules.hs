{-# LANGUAGE StrictData #-}

module CostAnalysis.Rules where

import CostAnalysis.Constraint
import CostAnalysis.Annotation
import Ast
import Data.Text(unpack)

data WeakenArg = Mono | L2xy | Neg
  deriving (Eq, Ord, Show)

data LetArg = NegE
  deriving (Eq, Ord, Show)

data Rule 
  = Const
  | ConstBase
  | Var
  | Ite 
  | Match 
  | Let [LetArg]
  | App 
  | TickNow 
  | TickDefer
  | WeakenVar
  | Weaken [WeakenArg]
  | ShiftConst
  | ShiftTerm 
  deriving(Eq, Show)

data RuleApp
  = ExprRuleApp Rule Bool (FreeAnn, FreeAnn) FreeAnn [Constraint] PositionedExpr
  | FunRuleApp PositionedFunDef
  | ProgRuleApp PositionedModule


-- printRuleApp :: Bool -> Maybe (Set Constraint, String -> String) -> RuleApp -> String
-- printRuleApp showCs integrateCore (ExprRuleApp rule cf q q' cs e) =
--   case integrateCore of
--     Just (unsatCore, highlight) ->
--       let unsatCs = unsat cs unsatCore
--           highlight' = if not . null $ unsatCs then highlight else id in
--         highlight' printRule ++ printCs unsatCs 
--     Nothing -> printRule ++ printCs cs
--   where printRule = show rule ++ printCf ++ printAnns ++": " ++ printExprHead e ++ " (" ++ printPos srcPos ++ ")"
--         printAnns = " [" ++ printMix q ++ " |- " ++ printMix q' ++ "]"
--         printCs cs = if showCs then
--           "\n\t" ++ intercalate ",\n\t" (map printConstraint cs)
--           else ""
--         unsat cs core = S.toList (S.fromList cs `S.intersection` core)
--         printQ (t, q) = intercalate "," (map unpack (q^.args)) ++ " : " ++ "q" ++ show (q^.annId) ++ "|" ++ show t
--         printMix ctx = intercalate "," $ map printQ (M.assocs ctx)
--         printCf = if cf then " (cf)" else ""
--         srcPos = case peSrc $ getAnn e of
--           Loc pos -> pos
--           DerivedFrom pos -> pos

{-# DEPRECATED #-}          
printRuleApp _ _ (FunRuleApp (Fn name _ _)) = "Fun: " ++ unpack name
printRuleApp _ _ (ProgRuleApp _) = "Prog" 
