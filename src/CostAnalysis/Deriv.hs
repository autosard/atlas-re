{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
--{-# LANGUAGE FlexibleContexts #-}


module CostAnalysis.Deriv where


import qualified Data.Tree as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Text as Text
import Prelude hiding (or)

import Ast hiding (Coefficient, CostAnnotation(..))
import Primitive(Id)
import Control.Monad.RWS

import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential hiding (Factor(..), emptyAnn, defaultAnn, defaultNegAnn, enrichWithDefaults)
import CostAnalysis.RsrcAnn hiding (fromAnn)
import CostAnalysis.Constraint ( ge,
                                 eq,
                                 or,
                                 Constraint,
                                 Term(ConstTerm) )
import CostAnalysis.Weakening
import CostAnalysis.ProveMonad
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe, mapMaybe)

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x
  
type ProofResult = (Derivation, [Constraint], RsrcSignature)

type TypeCtx = Map Id Type

type Prove e a = Tactic -> Bool -> TypeCtx -> e -> RsrcAnn -> RsrcAnn -> ProveMonad a

proveConst :: Prove PositionedExpr Derivation
proveConst _ cf ctx e@Error q q' = do
  let cs = annLikeUnify q q'
  conclude R.Const cf q q' cs e []
proveConst _ cf ctx e q q' = do
  pot <- view potential
  cs <- case cConst pot e q q' of
        Right cs -> return cs
        Left err -> errorFrom (SynExpr e) err
  conclude R.Const cf q q' cs e []

proveCmp :: Prove PositionedExpr Derivation
proveCmp _ cf _ e q q' = do
  unless (isBool $ getType e) $
    errorFrom (SynExpr e) "(cmp) applied to non-boolean expression."
  let cs = annEq q q'
  conclude R.Cmp cf q q' cs e []

proveVar :: Prove PositionedExpr Derivation
proveVar _ cf ctx e@(Var id) q q' = do
  when (M.notMember id ctx) $ errorFrom (SynExpr e) $ "(var) applied for variable '" ++ Text.unpack id ++ "' that is not in the context."
  let cs = annLikeUnify q q'
  conclude R.Var cf q q' cs e []

proveIte :: Prove PositionedExpr Derivation
proveIte tactic cf ctx e@(Ite (Var x) e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  let ctx' = M.delete x ctx
  deriv1 <- proveExpr t1 cf ctx' e1 q q'
  deriv2 <- proveExpr t2 cf ctx' e2 q q'
  conclude R.Ite cf q q' [] e [deriv1, deriv2]
proveIte tactic cf ctx e@(Ite (Coin p) e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  q1 <- enrichWithDefaults False "Q1" "" q
  q2 <- enrichWithDefaults False "Q2" "" q
  let cs = annLikeEq q (annLikeAdd
                            (annScalarMul q1 (ConstTerm p))
                            (annScalarMul q2 (ConstTerm (1-p))))
  deriv1 <- proveExpr t1 cf ctx e1 q1 q'
  deriv2 <- proveExpr t2 cf ctx e2 q2 q'
  conclude R.Ite cf q q' cs e [deriv1, deriv2]

proveMatchArm :: Id -> Prove PositionedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf ctx
  (MatchArm pat@(ConstPat _ id patVars) e) q q' = do
  pot <- view potential
  let tMatch = getType pat
  let vars = mapMaybe getVar patVars
  let ctx' = M.delete matchVar ctx `M.union` M.fromList vars
  p_ <- emptyAnn "P" "match arm" (M.toAscList ctx')
  let vars' = filter (\(x, t) -> bearesPotential pot t) vars
  let (p, cs) = cMatch pot q p_ matchVar (map fst vars')
  tellCs cs
  deriv <- proveExpr tactic cf ctx' e p q'
  return (cs, deriv)
  where getVar :: PositionedPatternVar -> Maybe (Id, Type)
        getVar v@(Id _ id) = Just (id, getType v)
        getVar (WildcardVar _) = Nothing
proveMatchArm matchVar tactic cf ctx arm@(MatchArm pat@(Alias _ x) e) q q' = do
  if M.member x ctx then do
    deriv <- proveExpr tactic cf ctx e q q'
    return ([], deriv)
  else errorFrom (SynArm arm) "found invalid alias (variable not previously defined) in match arm."
proveMatchArm _ _ _ _ arm _ _ = errorFrom (SynArm arm) "unsupported pattern match in rule (match)."

proveMatch :: Prove PositionedExpr Derivation
proveMatch tactic cf ctx e@(Match (Var x) arms) q q' = do
  pot <- view potential
  let tactics = subTactics (length arms) tactic
  results <- zipWithM proveArmWithTactic tactics arms
  let (cs, derivs) = foldr accum ([], []) results
  conclude R.Match cf q q' cs e derivs
  
  where accum (cs, deriv) (css, derivs) = (cs ++ css, deriv:derivs)
        proveArmWithTactic tactic arm = proveMatchArm x tactic cf ctx arm q q'


splitLetCtx :: TypeCtx -> PositionedExpr -> PositionedExpr -> ProveMonad (TypeCtx, TypeCtx)
splitLetCtx ctx e1 e2 = do
  let varsE1 = freeVars e1
  let ctxE1 = M.restrictKeys ctx varsE1
  let ctxE2 = ctx M.\\ ctxE1
  return (ctxE1, ctxE2)

   
proveLet :: Prove PositionedExpr Derivation
proveLet tactic@(Rule (R.Let letArgs) _) cf ctx e@(Let x e1 e2) q q' = do
  pot <- view potential
  if bearesPotential pot $ getType e1 then do
    let [t1, t2] = subTactics 2 tactic
    (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2
    let (gamma, delta) = (M.toAscList ctxE1, M.toAscList ctxE2)
    let ctxE2' = M.insert x (getType e1) ctxE2
      
    p_ <- emptyAnn "P" "let:base e1" gamma
    p' <- defaultAnn  "P'"  "let:base e1" [("e", getType e1)]
    r_ <- emptyAnn "R" "let:base e2" (M.toAscList ctxE2')
      
    let rangeD = rangeA . ranges $ pot
    let rangeE = if R.NegE `elem` letArgs then
         rangeBNeg . ranges $ pot else rangeB . ranges $ pot
      
    let bdes = forAllCombinations pot q (M.keys ctxE2) (rangeD, rangeE) x
      
    ps_ <- annArrayFromIdxs bdes "P" (M.toAscList ctxE1)
    ps'_ <- annArrayFromIdxs bdes "P'" [("e", getType e1)]

    let (p, pCs) = cLetBinding pot q p_ 
    deriv1 <- proveExpr t1 cf ctxE1 e1 p p'

    let (ps, ps', cfCs) = cLetCf pot q ps_ ps'_ x (map fst gamma, map fst delta) bdes
    cfDerivs <- zipWithM (proveExpr t1 True ctxE1 e1) (elems ps) (elems ps')
      
    let (r, rCs) = cLetBody pot q r_ p p' ps' x bdes
    deriv2 <- proveExpr t2 cf ctxE2' e2 r q'

    conclude (R.Let letArgs) cf q q' (pCs ++ rCs ++ cfCs) e ([deriv1, deriv2] ++ cfDerivs)
  -- let:base
  else do
    let [t1, t2] = subTactics 2 tactic
    (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2
    let ctxE2' = M.insert x (getType e1) ctxE2 

    p_ <- emptyAnn "P" "let:base e1" (M.toAscList ctxE1)
    p' <- defaultAnn  "P'"  "let:base e1" []
    r_ <- emptyAnn "R" "let:base e2" (M.toAscList ctxE2')
      
    let (p, pCs) = cLetBindingBase pot q p_ 
    deriv1 <- proveExpr t1 cf ctxE1 e1 p p'
    let (r, rCs) = cLetBodyBase pot q r_ p'
    deriv2 <- proveExpr t2 cf ctxE2' e2 r q'

    conclude (R.Let letArgs) cf q q' (pCs ++ rCs) e [deriv1, deriv2]

proveApp :: Prove PositionedExpr Derivation
proveApp tactic False ctx e@(App id _) q q' = do
  pot <- view potential
  fnSig <- use sig
  let (p, p') = withCost $ fnSig M.! id
  let (r, r') = withoutCost $ fnSig M.! id
  
  k <- freshVar
  let cs =
        or (concatMap (eq k . ConstTerm) [0,1,2])
        --or (eq k (ConstTerm 0) ++ ge k (ConstTerm 1))
        ++ annLikeUnify q (annAdd p (annScalarMul r k))
        ++ annLikeUnify q' (annAdd p' (annScalarMul r' k))
  conclude R.App False q q' cs e []
proveApp tactic True ctx e@(App id _) q q' = do
  pot <- view potential
  fnSig <- use sig
  let (p, p') = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs =
        or (concatMap (eq k . ConstTerm) [0,1,2])
        --or (eq k (ConstTerm 0) ++ ge k (ConstTerm 1))
        ++ annLikeUnify q (annScalarMul p k)
        ++ annLikeUnify q' (annScalarMul p' k)
  conclude R.App True q q' cs e []

redundentVars :: RsrcAnn -> Expr a -> Set Id
redundentVars q e = S.fromList (annVars q) S.\\ freeVars e

proveWeakenVar :: Prove PositionedExpr Derivation
proveWeakenVar tactic cf ctx e q q' = do
  pot <- view potential
  let redundant = redundentVars q e
  var <- if S.null redundant then
        errorFrom (SynExpr e) "Could not find a redundant variable to eleminate with the (w:var) rule."
        else
        return $ S.elemAt 0 redundant
  let ctx' = M.delete var ctx 
  let [t] = subTactics 1 tactic
  
  r_ <- emptyAnn "R" "weaken var" (M.toAscList ctx')
  let (r,cs) = cWeakenVar pot q r_
  
  deriv <- proveExpr t cf ctx' e r q'
  conclude R.WeakenVar cf q q' cs e [deriv]
  
proveWeaken :: Prove PositionedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) cf ctx e q q' = do
  pot <- view potential
  let [t] = subTactics 1 tactic
  let wArgs' = S.fromList wArgs
  let neg = R.Neg `S.member` wArgs'
  
  p <- enrichWithDefaults neg "P" "" q
  -- p <= q
  pCs <-  farkas pot wArgs' (p^.coeffs) p q
  
  p' <- enrichWithDefaults neg "P'" "" q'
  -- q' <= p'
  p'Cs <-  farkas pot wArgs' (p'^.coeffs) q' p'
  
  deriv <- proveExpr t cf ctx e p p'
  conclude (R.Weaken wArgs) cf q q' (pCs ++ p'Cs) e [deriv]

proveShift :: Prove PositionedExpr Derivation
proveShift tactic cf ctx e q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic

  k <- freshVar
  
  p_ <- emptyAnn "P" "" (q^.args)
  let (p, pCs) = eqMinus pot p_ q k
  p'_ <- emptyAnn "P'" "" (q'^.args)
  let (p', p'Cs) = eqMinus pot p'_ q' k
  
  let cs = ge k (ConstTerm 0) ++ pCs ++ p'Cs
  deriv <- proveExpr subTactic cf ctx e p p'
  conclude R.Shift cf q q' cs e [deriv]

proveTickDefer :: Prove PositionedExpr Derivation
proveTickDefer tactic cf ctx e@(Tick c e1) q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic
  if cf then do
    deriv <- proveExpr subTactic cf ctx e1 q q'
    conclude R.TickDefer cf q q' [] e [deriv]
  else do
    p_ <- emptyAnn "P" "" (q'^.args)
    let (p, cs) = eqPlus pot p_ q' (ConstTerm (fromMaybe 1 c))

    deriv <- proveExpr subTactic cf ctx e1 q p

    conclude R.TickDefer cf q q' cs e [deriv]

removeRedundantVars :: Prove PositionedExpr Derivation -> Prove PositionedExpr Derivation
removeRedundantVars prove tactic cf ctx e q q' = if (not . null) (redundentVars q e) then
  proveWeakenVar (Rule R.WeakenVar [tactic]) cf ctx e q q'
  else prove tactic cf ctx e q q'


proveExpr :: Prove PositionedExpr Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var []) cf ctx e@(Var _) = removeRedundantVars proveVar tactic cf ctx e
proveExpr tactic@(Rule R.Cmp []) cf ctx e@(Const {}) | isCmp e = proveCmp tactic cf ctx e
--proveExpr tactic@(Rule R.Const []) cf ctx e@(Tuple {}) = removeRedundantVars provePair tactic cf ctx e

proveExpr tactic@(Rule R.Const []) cf ctx e@(Const {}) = removeRedundantVars proveConst tactic cf ctx e 
proveExpr tactic@(Rule R.Match _) cf ctx e@(Match {}) = proveMatch tactic cf ctx e
proveExpr tactic@(Rule R.Ite _) cf ctx e@(Ite {}) = proveIte tactic cf ctx e
proveExpr tactic@(Rule (R.Let _) _) cf ctx e@(Let {}) = proveLet tactic cf ctx e
proveExpr tactic@(Rule R.TickDefer _) cf ctx e@(Tick {}) = removeRedundantVars proveTickDefer tactic cf ctx e
proveExpr tactic@(Rule R.WeakenVar _) cf ctx e = proveWeakenVar tactic cf ctx e
proveExpr tactic@(Rule (R.Weaken _) _) cf ctx e = proveWeaken tactic cf ctx e
proveExpr tactic@(Rule R.Shift _) cf ctx e = proveShift tactic cf ctx e
proveExpr tactic@(Rule R.App _) cf ctx e@(App {}) = removeRedundantVars proveApp tactic cf ctx e
proveExpr Auto cf ctx e = proveByAuto cf ctx e
proveExpr tactic _ _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"

-- auto tactic
proveByAuto :: Bool -> TypeCtx -> PositionedExpr -> RsrcAnn -> RsrcAnn -> ProveMonad Derivation
proveByAuto cf ctx e q q' = do
  let tactic = genTactic e
  proveExpr tactic cf ctx e q q'

genTactic :: PositionedExpr -> Tactic
genTactic e@(Var {}) = autoWeaken e (Rule R.Var [])
genTactic e@(Const {}) | isCmp e = Rule R.Cmp []
genTactic e@(Const {}) = autoWeaken e (Rule R.Const [])
genTactic (Match _ arms) = Rule R.Match $ map (genTactic . armExpr) arms
genTactic e@(Ite _ e2 e3) = let t1 = genTactic e2
                                t2 = genTactic e3 in
  autoWeaken e $ Rule R.Ite [t1, t2]
genTactic (App {}) = Rule R.Shift [Rule R.App []]
genTactic e@(Let _ binding body) = let t1 = genTactic binding
                                       t2 = genTactic body
                                       ctx = peCtx $ getAnn e 
                                       neg = S.member BindsAppOrTickRec ctx in
  autoWeaken e $ Rule (R.Let [R.NegE | neg]) [t1, t2]
genTactic (Tick _ e) = Rule R.TickDefer [genTactic e]

autoWeaken :: PositionedExpr -> Tactic -> Tactic
autoWeaken e tactic = case wArgsForExpr e of
  [] -> tactic
  wArgs -> Rule (R.Weaken wArgs) [tactic]

wArgsForExpr :: PositionedExpr -> [R.WeakenArg]
wArgsForExpr e = S.toList $ foldr checkCtx S.empty
  [ ([PseudoLeaf], [R.Mono]),
    ([BindsAppOrTickRec], [R.Neg]),
    ([BindsAppOrTick], [R.Mono, R.L2xy]),
    ([FirstAfterApp, OutermostLet], [R.L2xy, R.Mono]),
    ([FirstAfterMatch], [R.Mono]),
    ([IteCoin], [R.L2xy])]
  where ctx = peCtx $ getAnn e
        checkCtx (flags, impliedArgs) wArgs = if all (`S.member` ctx) flags then
          S.union wArgs (S.fromList impliedArgs) else wArgs


ctxFromProdType :: Type -> [Id] -> TypeCtx
ctxFromProdType (TAp Prod ts) args = M.fromList $ zip args ts
ctxFromProdType t _ = error $ "Cannot construct a type context from the non product type '" ++ show t ++ "'."

proveFunBody :: Prove PositionedFunDef Derivation
proveFunBody _ cf _ (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  let ctx = ctxFromProdType tFrom args
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic cf ctx e q q'

proveFun :: PositionedFunDef -> ProveMonad Derivation
proveFun fun@(FunDef _ fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  
  -- prove both with and without costs for well-typedness
  let (p, p') = withoutCost ann
  derivCf <- proveFunBody Auto True M.empty fun p p'
  
  let (q, q') = withCost ann  
  deriv <- proveFunBody Auto False M.empty fun q q'
  
  return $ T.Node (R.FunRuleApp fun) [derivCf, deriv]
