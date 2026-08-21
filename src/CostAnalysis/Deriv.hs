{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Deriv where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set(Set)
import Prelude hiding (or, and, negate, sum)
import Lens.Micro.Platform
import Data.Maybe (fromMaybe)
import Control.Monad (zipWithM)


import Primitive(Id, substVar, freeVars)
import Syntax.Ast

import Syntax.Measure (ConstPat(..))
import CostAnalysis.Tactic
import CostAnalysis.Rules (JudgementType(..))
import qualified CostAnalysis.Rules as R
import CostAnalysis.Template hiding (assertEqSubst)
import CostAnalysis.Constraint ( ArithExpr(ConstTerm), sum ) 
                                 
import CostAnalysis.ProveMonad
import qualified CostAnalysis.Rules as Rule
import CostAnalysis.Subtyping



type Prove e a = Tactic -> e -> JudgementType -> Id -> FreeTemplate -> FreeTemplate -> ProveMonad a


proveVar :: Prove PositionedExpr Derivation
proveVar _ e@(Var x) judgeType binder q q' = do
  let cs = assertEqVarSubst binder x q' q
  conclude R.Var judgeType q q' cs e []


proveConst :: Prove PositionedExpr Derivation
proveConst _ e@(Const name args) judgeType binder q q' = do
  mEnv <- measureEnvForType (getType e)
  let subst = ExpandCtor (ConstPat name (map argToVar args)) mEnv
  cs <- assertEqSubst (binder, subst) q' q
  conclude R.Const judgeType q q' cs e []
  where argToVar (Var x) = x
        argToVar _ = error "Encoutered non variable argument for constructor application."


proveIte :: Prove PositionedExpr Derivation
proveIte tactic e@(Ite (Coin p) e1 e2) judgeType binder q q' = do
  let [t1, t2] = subTactics 2 tactic
  q1 <- freshFrom q
  q2 <- freshFrom q
  let cs = assertEq q $ add 
        (scale q1 (ConstTerm p))
        (scale q2 (ConstTerm (1-p)))
  deriv1 <- proveExpr t1 e1 judgeType binder q1 q'
  deriv2 <- proveExpr t2 e2 judgeType binder q2 q'
  conclude R.IteCoin judgeType q q' cs e [deriv1, deriv2]
proveIte tactic e@(Ite e1 e2 e3) judgeType binder q q' = do
  let [_, t2, t3] = subTactics 3 tactic
  deriv2 <- proveExpr t2 e2 judgeType binder q q'
  deriv3 <- proveExpr t3 e3 judgeType binder q q'
  conclude R.Ite judgeType q q' [] e [deriv2, deriv3]


simplifyPattern :: Pattern Positioned -> ProveMonad ConstPat
simplifyPattern p@(PConst _ id ps) = ConstPat id <$> mapM toVar ps
  where toVar (PVar _ x) = return x
        toVar (PWildcard _) = return "_"
        toVar _ = errorFrom (SynPat p) $ "Analysis does not support nested patterns."


proveMatchArm :: Id -> Prove PositionedMatchArm Derivation
proveMatchArm x tactic arm@(MatchArm pat@(PVar _ y) body) judgeType binder q q' = do
  p <- freshFrom (substVar x y q)
  let cs = assertEqVarSubst x y q p 
  deriv <- proveExpr tactic body judgeType binder p q'
  concludeArm pat judgeType q q' cs body [deriv]
proveMatchArm x tactic (MatchArm pat body) judgeType binder q q' = do
  let tMatch = getType pat
  mEnv <- measureEnvForType tMatch
  subst <- (`ExpandCtor`  mEnv) <$> simplifyPattern pat
  (p, cs) <- defEqSubst (x, subst) q
  deriv <- proveExpr tactic body judgeType binder p q'
  concludeArm pat judgeType q q' cs body [deriv]
proveMatchArm _ _ arm _ _ _ _ = errorFrom (SynArm arm) "unsupported pattern in rule (match)."


proveMatch :: Prove PositionedExpr Derivation
proveMatch tactic e@(Match (Var x) arms) judgeType binder q q' = do
  let tactics = subTactics (length arms) tactic
  derivs <- zipWithM proveArmWithTactic tactics arms
  conclude R.Match judgeType q q' [] e derivs
  where proveArmWithTactic tactic arm = proveMatchArm x tactic arm judgeType binder q q'
  

proveLet :: Prove PositionedExpr Derivation
proveLet tactic e@(Let x e1 e2) judgeType binder q q' = do
  let [t1, t2] = subTactics 2 tactic
      argsO = S.fromList (args q) S.\\ (freeVars e1 S.\\ freeVars e2)
  o <- freshTempl (x : S.toList argsO)
  deriv1 <- proveExpr t1 e1 judgeType x q o
  deriv2 <- proveExpr t2 e2 judgeType binder o q'
  conclude R.Let judgeType q q' [] e [deriv1, deriv2]
  

proveApp :: Prove PositionedExpr Derivation
proveApp tactic e@(App "error" _) judgeType binder q q' = do
  conclude R.App judgeType q q' [] e []
proveApp tactic e@(App fn appArgs) judgeType binder q q' = do
  fnSig <- (M.! fn) <$> use sig
  mSizeSig <- M.lookup fn <$> use sizeSig
  let appVars = map argToVar appArgs

  [p, r, p', r'] <- mapM freshFrom [q, q, q', q']
  let csSplit = assertEq q (add p r) ++ assertEq q' (add p' r')
  
  csRemainder <- case mSizeSig of
    -- transform left over terms
    Nothing -> return $ assertEq r' r
    Just st -> do
      let subst = TransformApp appVars st
      assertEqSubst (binder, subst) r' r
  
  -- check signature
  let csSig = assertEqVarsSubst (fnSig^.fsFormArgs)
              appVars
              (fnSig^.fsFrom)
              p
        ++ assertEqVarsSubst [fnSig^.fsBinder] [binder] (fnSig^.fsTo) p'

  conclude R.App judgeType q q' (csSplit ++ csRemainder ++ csSig) e []
  where argToVar :: Expr Positioned -> Id
        argToVar (Var x) = x
        argToVar expr = error $ "Encoutered non variable argument for function application: " ++ printExprPlain expr

  
proveSub :: Prove PositionedExpr Derivation
proveSub tactic@(Rule (Rule.Sub sArgs) _) e judgeType binder q q' = do
  let [t] = subTactics 1 tactic
  p <- freshTempl (args q)
  cs <- templLe (S.fromList sArgs) p q
  deriv <- proveExpr t e judgeType binder p q'
  conclude (R.Sub sArgs) judgeType q q' cs e [deriv]


proveShift :: Prove PositionedExpr Derivation
proveShift tactic e judgeType binder q q' = do
  let [subTactic] = subTactics 1 tactic
  k <- freshVar
  let shift s = sum [s,k]
  (p, cs1) <- defineByShift shift q
  (p', cs2) <- defineByShift shift q'
  deriv <- proveExpr subTactic e judgeType binder p p'
  conclude R.Shift judgeType q q' (cs1 ++ cs2) e [deriv]
  

proveTick :: Prove PositionedExpr Derivation
proveTick tactic e@(Tick c e1) judgeType binder q q' = do
  let [subTactic] = subTactics 1 tactic
  if isCostFree judgeType then do
    deriv <- proveExpr subTactic e1 judgeType binder q q'
    conclude R.Tick judgeType q q' [] e [deriv]
  else do
    let shift s = sum [s, ConstTerm (fromMaybe 1 c)]
    (p, cs) <- defineByShift shift q'
    deriv <- proveExpr subTactic e1 judgeType binder q p
    conclude R.Tick judgeType q q' cs e [deriv]


proveLit :: Prove PositionedExpr Derivation
proveLit tactic e@(Lit _) judgeType binder q q' = do
  let cs = assertEq q q'
  conclude R.Lit judgeType q q' cs e []


proveExpr :: Prove (Expr Positioned) Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var [])    e@(Var _)    jt = proveVar tactic e jt
proveExpr tactic@(Rule R.Const [])  e@(Const {}) jt = proveConst tactic e jt
proveExpr tactic@(Rule R.Match _)   e@(Match {}) jt = proveMatch tactic e jt
proveExpr tactic@(Rule R.Ite _)     e@(Ite {})   jt = proveIte tactic e jt
proveExpr tactic@(Rule R.Let _)     e@(Let {})   jt = proveLet tactic e jt
proveExpr tactic@(Rule R.Tick _)    e@(Tick {})  jt = proveTick tactic e jt
proveExpr tactic@(Rule (R.Sub _) _) e            jt = proveSub tactic e jt
proveExpr tactic@(Rule R.Shift _)   e            jt = proveShift tactic e jt
proveExpr tactic@(Rule R.App _)     e@(App id _) jt = proveApp tactic e jt
proveExpr tactic@(Rule R.Lit [])    e@(Lit _)    jt = proveLit tactic e jt
-- auto tactic
proveExpr Auto e judgeType = proveExpr (genTactic judgeType e) e judgeType
proveExpr tactic e _ = \_ _ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"

genTactic :: JudgementType -> PositionedExpr -> Tactic
genTactic judgeType e@(Var {}) = autoSub judgeType e (Rule R.Var [])
genTactic judgeType e@(Const {}) = autoSub judgeType e (Rule R.Const [])
genTactic judgeType (Match _ arms) = Rule R.Match $ map (genTactic judgeType . armExpr) arms
genTactic judgeType e@(Ite (Coin _) e2 e3) =
  let t1 = genTactic judgeType e2 
      t2 = genTactic judgeType e3
      tactic = Rule R.Ite [t1, t2] in
  autoSub judgeType e tactic
genTactic judgeType e@(Ite e1 e2 e3) =
  let t1 = genTactic judgeType e1 
      t2 = genTactic judgeType e2 
      t3 = genTactic judgeType e3
      tactic = Rule R.Ite [t1, t2, t3] in
  autoSub judgeType e tactic
genTactic judgeType e@(App {}) = autoSub judgeType e $
  Rule R.Shift [Rule R.App []]
genTactic judgeType e@(Let _ binding body) =
  let tBinding = genTactic judgeType binding
      tBody = genTactic judgeType body in
  autoSub judgeType e $ Rule R.Let [tBinding, tBody]
genTactic judgeType (Tick _ e) = Rule R.Tick [genTactic judgeType e]
genTactic judgeType e@(Lit _) = Rule R.Lit []
genTactic _ e = error $ "genTactic: " ++ printExprHead e 

autoSub :: JudgementType -> PositionedExpr -> Tactic -> Tactic
autoSub judgeType e tactic = case subArgsForExpr e judgeType of
  [] -> tactic
  wArgs -> Rule (R.Sub wArgs) [tactic]

subArgsForExpr :: Expr Positioned -> JudgementType -> [R.SubArg]
subArgsForExpr e judgeType = S.toList $ foldr checkCtx S.empty (subArgMap judgeType)
  where ctx :: Set ExprCtx
        ctx = peCtx $ getAnn e
        checkCtx (flags, impliedArgs) subArgs = if all (`S.member` ctx) flags then
          S.union subArgs (S.fromList impliedArgs) else subArgs

subArgMap :: JudgementType -> [([ExprCtx], [R.SubArg])]
subArgMap Standard =
  [ ([PseudoLeaf], [R.Mono]),
    ([BindsAppOrTick], [R.Mono, R.L2xy]),
    ([FirstAfterApp, OutermostLet], [R.L2xy, R.Mono]),
    ([FirstAfterMatch], [R.Mono]),
    ([IteCoin], [R.L2xy])]
subArgMap Cf = [([FirstAfterMatch], [R.Mono])]
subArgMap CfEq = []
 
proveFun :: FunSig -> PositionedFunDef -> JudgementType -> ProveMonad Derivation
proveFun fnTSig funDef judgeType = do
  fnSig <- (M.! (funDef^.funName)) <$> use sig
  tactic <- fromMaybe Auto . M.lookup (funDef^.funName) <$> view tactics
  
  proveExpr
    tactic
    (funDef^.funBody)
    judgeType
    (fnSig^.fsBinder)
    (fnSig^.fsFrom)
    (fnSig^.fsTo)
 
