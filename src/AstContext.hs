module AstContext where

import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import StaticAnalysis(calledFunctions')
import Ast


contextualizeMod :: TypedModule -> PositionedModule
contextualizeMod = modMap contextualizeFun

contextualizeFun :: TypedFunDef -> PositionedFunDef
contextualizeFun (FunDef ann id args body) = FunDef ann id args (contextualizeExpr id body)

contextualizeExpr :: Id -> TypedExpr -> PositionedExpr
contextualizeExpr fn = contextualizeExpr' fn $ S.fromList [PseudoLeaf, OutermostLet]

contextualizeExpr' :: Id -> Set ExprCtx -> TypedExpr -> PositionedExpr
contextualizeExpr' fn ctx (VarAnn ann id) = VarAnn (extendWithCtx (S.delete OutermostLet ctx) ann) id
contextualizeExpr' fn ctx (LitAnn ann l) = LitAnn (extendWithCtx (S.delete OutermostLet ctx) ann) l
contextualizeExpr' fn ctx (ConstAnn ann id args) = ConstAnn (extendWithCtx ctx ann) id args'
  where args' = map (contextualizeExpr' fn ctx) args
contextualizeExpr' fn ctx (IteAnn ann e1 e2 e3) = IteAnn (extendWithCtx coinCtx ann) e1' e2' e3'
  where coinCtx = if isCoin e1 then S.singleton IteCoin else S.empty
        ctx' = S.insert FirstAfterMatch ctx
        e1' = contextualizeExpr' fn ctx' e1
        e2' = contextualizeExpr' fn ctx' e2
        e3' = contextualizeExpr' fn ctx' e3
contextualizeExpr' fn ctx (MatchAnn ann e arms) = MatchAnn (extendWithCtx S.empty ann) e' arms'
  where ctx' = S.insert FirstAfterMatch ctx
        e' = contextualizeExpr' fn ctx' e
        arms' = map (contextualizeArm fn ctx') arms
contextualizeExpr' fn ctx (LetAnn ann id e1 e2) = LetAnn (extendWithCtx letCtx ann) id e1' e2'
  where outermost = [OutermostLet | S.member OutermostLet ctx,
                                    nestedConst e1 e2]
        bindsApp = [BindsAppOrTick | appOrTick e1]
        bindsAppRec = [BindsAppOrTickRec
                      | appOrTick e1,
                        S.member fn (calledFunctions' e1)]
        firstAfterMatch = [FirstAfterMatch | S.member FirstAfterMatch ctx,
                                             (not . isCmp) e1]
        firstAfterApp = [FirstAfterApp | S.member FirstAfterApp ctx]
        letCtx = S.fromList $ outermost ++ bindsApp ++ bindsAppRec ++ firstAfterMatch ++ firstAfterApp
        childCtx = ctx S.\\ S.fromList (FirstAfterMatch:[OutermostLet | nestedConst e1 e2]
                                        ++ [FirstAfterApp | S.member FirstAfterMatch ctx])
        bodyCtx = if appOrTick e1 then S.insert FirstAfterApp childCtx else childCtx
        e1' = contextualizeExpr' fn (S.delete PseudoLeaf childCtx) e1
        e2' = contextualizeExpr' fn bodyCtx e2
contextualizeExpr' fn ctx (AppAnn ann id args) = AppAnn (extendWithCtx S.empty ann) id args'
  where args' = map (contextualizeExpr' fn ctx) args
contextualizeExpr' fn ctx (TickAnn ann c e) = TickAnn (extendWithCtx S.empty ann) c e'
  where e' = contextualizeExpr' fn ctx e
contextualizeExpr' fn ctx (CoinAnn ann p) = CoinAnn (extendWithCtx S.empty ann) p 

isCoin :: Expr a -> Bool
isCoin (Coin _) = True
isCoin _ = False

nestedConst :: Expr a -> Expr a -> Bool
nestedConst (Const {}) (Const {}) = True
nestedConst (Const {}) (Let _ e1 e2) = nestedConst e1 e2
nestedConst _ _ = False

appOrTick :: Expr a -> Bool                                                 
appOrTick (Tick {}) = True
appOrTick (App {}) = True
appOrTick _ = False

contextualizeArm :: Id -> Set ExprCtx -> TypedMatchArm -> PositionedMatchArm
contextualizeArm fn ctx (MatchArmAnn ann pat e) = MatchArmAnn (extendWithCtx S.empty ann) pat' e'
  where pat' = contextualizePattern pat
        e' = contextualizeExpr' fn ctx e

contextualizePattern :: TypedPattern -> PositionedPattern
contextualizePattern (ConstPat ann id args) = ConstPat (extendWithCtx S.empty ann) id args'
  where args' = map contextualizePatternVar args
contextualizePattern (Alias ann id)  = Alias (extendWithCtx S.empty ann) id
contextualizePattern (WildcardPat ann)  = WildcardPat (extendWithCtx S.empty ann) 

contextualizePatternVar :: TypedPatternVar -> PositionedPatternVar
contextualizePatternVar (Id ann id) = Id (extendWithCtx S.empty ann) id
contextualizePatternVar (WildcardVar ann) = WildcardVar (extendWithCtx S.empty ann)
