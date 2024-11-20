{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Deriv where

import qualified Data.List as L
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as Text
import Prelude hiding (or, and)

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
import CostAnalysis.Constraint ( and,
                                 or,
                                 le,
                                 Constraint,
                                 Term(ConstTerm), geZero )
import CostAnalysis.Weakening
import CostAnalysis.ProveMonad
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe, mapMaybe, isJust)

import Debug.Trace hiding (traceShow)
import Data.Tuple (swap)
import Data.List.Extra (groupSort)

traceShow x = trace (show x) x
  
type ProofResult = (Derivation, [Constraint], RsrcSignature)

type Prove e a = Tactic -> Maybe Int -> e -> AnnCtx -> AnnCtx -> ProveMonad a

proveConst :: Prove PositionedExpr Derivation
proveConst _ cf e@Error q q' = do
  let cs = ctxUnify q q'
  conclude R.Const cf q q' cs e []
proveConst _ cf e@(Const "(,)" args) q q' = do
  let argsByType = M.fromList . groupSort $ map (swap . varWithType) args
  let cs = ctxUnify' q q' argsByType
  conclude R.Const cf q q' cs e []
proveConst _ cf e@(Const id _) q q' = do
  pots <- use potentials
  let t = getType e
  cs <- (ctxUnify (M.delete t q) (M.delete t q') ++)
    <$> if M.member t pots then
          return $ cConst (potForType t pots) e (q M.! t) (q' M.! t)
        else errorFrom (SynExpr e) $ "Constructor '" ++ Text.unpack id ++ "' not supported, by selected potential function(s)."
  conclude R.Const cf q q' cs e []

proveCmp :: Prove PositionedExpr Derivation
proveCmp _ cf e q q' = do
  unless (isBool $ getType e) $
    errorFrom (SynExpr e) "(cmp) applied to non-boolean expression."
  let cs = ctxUnify q q'
  conclude R.Cmp cf q q' cs e []

proveVar :: Prove PositionedExpr Derivation
proveVar _ cf e@(Var id) q q' = do
  let cs = ctxUnify q q'
  conclude R.Var cf q q' cs e []

proveIte :: Prove PositionedExpr Derivation
proveIte tactic cf e@(Ite (Coin p) e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  q1 <- enrichWithDefaults False "Q1" "" q
  q2 <- enrichWithDefaults False "Q2" "" q
  let cs = ctxUnify q (ctxAdd
                     (ctxScalarMul q1 (ConstTerm p))
                     (ctxScalarMul q2 (ConstTerm (1-p))))
  deriv1 <- proveExpr t1 cf e1 q1 q'
  deriv2 <- proveExpr t2 cf e2 q2 q'
  conclude R.Ite cf q q' cs e [deriv1, deriv2]
proveIte tactic cf e@(Ite _ e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  deriv1 <- proveExpr t1 cf e1 q q'
  deriv2 <- proveExpr t2 cf e2 q q'
  conclude R.Ite cf q q' [] e [deriv1, deriv2]

proveMatchArm :: Id -> Prove PositionedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf 
  (MatchArm pat@(ConstPat _ id patVars) e) q q' = do
  let tMatch = getType pat
  let nonMatchAnns = M.delete tMatch q
  let matchAnn = q M.! tMatch
  pot <- potForType tMatch <$> use potentials
  let vars = mapMaybe (getVar tMatch) patVars
  let args' = L.delete matchVar (matchAnn ^.args) `L.union` vars
  p_ <- emptyAnn tMatch "P" "match arm" args'
  let (p, cs) = cMatch pot matchAnn p_ matchVar vars
  tellCs cs
  deriv <- proveExpr tactic cf e (M.insert tMatch p nonMatchAnns) q'
  return (cs, deriv)
  where getVar :: Type -> PositionedPatternVar -> Maybe Id
        getVar t v@(Id _ id) | matchesType (getType v) t = Just id
                             | otherwise = Nothing
        getVar _ (WildcardVar _) = Nothing
proveMatchArm matchVar tactic cf arm@(MatchArm pat@(Alias _ x) e) q q' = do
    deriv <- proveExpr tactic cf e q q'
    return ([], deriv)
proveMatchArm _ _ _ arm _ _ = errorFrom (SynArm arm) "unsupported pattern match in rule (match)."

proveMatch :: Prove PositionedExpr Derivation
proveMatch tactic cf e@(Match (Var x) arms) q q' = do
  let tactics = subTactics (length arms) tactic
  results <- zipWithM proveArmWithTactic tactics arms
  let (cs, derivs) = foldr accum ([], []) results
  conclude R.Match cf q q' cs e derivs
  
  where accum (cs, deriv) (css, derivs) = (cs ++ css, deriv:derivs)
        proveArmWithTactic tactic arm = proveMatchArm x tactic cf arm q q'


splitLetCtx :: PositionedExpr -> PositionedExpr -> RsrcAnn -> ([Id], [Id])
splitLetCtx e1 e2 q = 
  let qArgs = S.fromList (q^.args)
      varsE1 = freeVars e1
      argsE1 = qArgs `S.intersection` varsE1
      argsE2 = qArgs S.\\ argsE1 in
    (S.toList argsE1, S.toList argsE2)

isLeaf :: PositionedExpr -> Bool
isLeaf Leaf = True
isLeaf _ = False

proveLet :: Prove PositionedExpr Derivation
proveLet tactic@(Rule (R.Let letArgs) _) cf e@(Let x e1 e2) q q'
  | isProd (getType e1) = errorFrom (SynExpr e) "Binding product type in let expression is not supported."
  | otherwise = do
  pots <- use potentials
  let [t1, t2] = subTactics 2 tactic
  let argSplit = M.map (splitLetCtx e1 e2) q
  
  let nonBindingQ = M.delete (getType e1) q

  ctxP_ <- emptyAnnCtx (M.map fst argSplit) "P" "let:base e1"
  ctxR_ <- emptyAnnCtx (M.map snd argSplit) "R" "let:base e2"
  -- base
  nonBindingCtxP' <- defaultAnnCtx (M.map (const []) nonBindingQ) "P'"  "let:base e1"

  let (nonBindingCtxP, nonBindingCsP) = ctxDefineBinding ctxP_ nonBindingQ 
  let (nonBindingCtxR, nonBindingCsR) = ctxDefineBody ctxR_ nonBindingQ nonBindingCtxP nonBindingCtxP'
  let nonBindingCs = nonBindingCsP ++ nonBindingCsR
  
  -- potential bind
  (ctxP', ctxP, ctxR, cs, cfDerivs) <- case M.lookup (getType e1) q of
    Just bindingQ -> do
      potE1 <- potForType (getType e1) <$> use potentials
      let (gamma, delta) = argSplit M.! getType e1
      bindingP' <- defaultAnn (getType e1) "P'"  "let e1" ["e1"]
        
      let rangeD = rangeA . ranges $ potE1
      let rangeE = if R.NegE `elem` letArgs then
            rangeBNeg . ranges $ potE1 else rangeB . ranges $ potE1
      
      let is = letCfIdxs potE1 (q M.! getType e1) delta (rangeD, rangeE) x

      ps_ <- emptyArrayFromIdxs (getType e1) is "P" gamma
      ps'_ <- emptyArrayFromIdxs (getType e1) is "P'" ["e1"]

      r_ <-  emptyAnn (getType e1) "R" "let:base e2" (x:delta)

      let (p, pCs) = defineFrom' (ctxP_ M.! getType e1) bindingQ (const le)
      let (ps, ps', cfCs) = cLetCf potE1 bindingQ ps_ ps'_ x (gamma, delta) is
      let (r, rCs) = chainDef [
            cLetBodyUni bindingQ p bindingP' x,
            cLetBodyMulti potE1 ps' x is] r_ -- todo rename to cLetBindMulti
      let bindingCtxP' = M.insert (getType e1) bindingP' nonBindingCtxP'
      let bindingCtxP = M.insert (getType e1) p nonBindingCtxP
      let bindingCtxR = M.insert (getType e1) r nonBindingCtxR
      let ctxPs = map (\p -> M.insert (getType e1) p nonBindingCtxP) (elems ps)
      let ctxPs' = map (\p -> M.insert (getType e1) p nonBindingCtxP') (elems ps')

      cfDerivs <- zipWithM (proveExpr t1 (Just $ fromMaybe 0 cf) e1) ctxPs ctxPs'
      
      return (bindingCtxP', bindingCtxP, bindingCtxR,
               pCs ++ cfCs ++ rCs ++ nonBindingCs,
               cfDerivs)
      -- derivs
    Nothing -> return (nonBindingCtxP',
                       nonBindingCtxP,
                       nonBindingCtxR,
                       nonBindingCs, [])

  
  deriv1 <- proveExpr t1 cf e1 ctxP ctxP'
  deriv2 <- proveExpr t2 cf e2 ctxR q'

  conclude (R.Let letArgs) cf q q' cs e ([deriv1, deriv2] ++ cfDerivs)

proveApp :: Prove PositionedExpr Derivation
proveApp tactic Nothing e@(App id _) q q' = do
  fnSig <- use sig
  let cSig = withCost $ fnSig M.! id
  let cfSigs = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs = or $ concatMap (linCombOfSig cSig) cfSigs
  conclude R.App Nothing q q' cs e []
  where linCombOfSig (p, p') (r, r') = concat
          [and $
           ctxUnify q (ctxAdd p (ctxScalarMul r (ConstTerm k)))
           ++ ctxUnify q' (ctxAdd p' (ctxScalarMul r' (ConstTerm k)))
          | k <- [0,1,2]]
proveApp tactic (Just cf) e@(App id _) q q' = do
  fnSig <- use sig
  let cfSigs = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs = or $ linCombOfSig (q, q') (cfSigs L.!! cf)

  conclude R.App (Just cf) q q' cs e []
  where linCombOfSig (q, q') (p, p') = concat
          [ and $
            ctxUnify q (ctxScalarMul p (ConstTerm k))
            ++ ctxUnify q' (ctxScalarMul p' (ConstTerm k))
          | k <- [0,1,2]]

redundentVars :: AnnCtx -> Expr a -> [(Id, Type)]
redundentVars qs e =
  [ (x, t)
  | (t, q) <- M.toAscList qs,
    x <- annVars q,
    not $ x `S.member` freeVars e]

proveWeakenVar :: Prove PositionedExpr Derivation
proveWeakenVar tactic cf e q q' = do
  let redundant = redundentVars q e
  (var, tVar) <- if null redundant then
                errorFrom (SynExpr e) "Could not find a redundant variable to eleminate with the (w:var) rule."
              else
                return $ head redundant
  let [t] = subTactics 1 tactic
  let redundantQ = q M.! tVar
  pot <- potForType tVar <$> use potentials
  
  r_ <- emptyAnn tVar "R" "weaken var" $ L.delete var (annVars redundantQ)
  let (r,cs) = defineFrom r_ redundantQ
  let ctxR = M.insert tVar r q
  
  deriv <- proveExpr t cf e ctxR q'
  conclude R.WeakenVar cf q q' cs e [deriv]
  
proveWeaken :: Prove PositionedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) cf e q q' = do
  let [t] = subTactics 1 tactic
  let wArgs' = S.fromList wArgs
  let neg = R.Neg `S.member` wArgs'
  
  p <- enrichWithDefaults neg "P" "weaken" q
  -- p <= q
  pCs <-  ctxFarkas wArgs' p q
  
  p' <- enrichWithDefaults neg "P'" "weaken" q'
  -- q' <= p'
  p'Cs <-  ctxFarkas wArgs' q' p'
  
  deriv <- proveExpr t cf e p p'
  conclude (R.Weaken wArgs) cf q q' (pCs ++ p'Cs) e [deriv]

proveShift :: Prove PositionedExpr Derivation
proveShift tactic cf@Nothing e q q' = do
  let [subTactic] = subTactics 1 tactic

  k <- freshVar

  p_ <- emptyAnnCtx (M.map _args q) "P" "shift" 
  (ps, pCs) <- ctxDefByMinus p_ q k

  p'_ <- emptyAnnCtx (M.map _args q') "P'" "shift"
  (ps', p'Cs) <- ctxDefByMinus p'_ q' k

  let cs = pCs ++ p'Cs ++ geZero k
  
  deriv <- proveExpr subTactic cf e ps ps'
  conclude R.Shift cf q q' cs e [deriv]
proveShift tactic cf@(Just _) e q q' = do
  let [subTactic] = subTactics 1 tactic
  let wArgs = S.fromList [R.Mono]

  p <- fromCtx "P" "shift" q 
  pCs <- ctxFarkas wArgs p q

  p' <- fromCtx "P'" "shift" q'
  p'Cs <- ctxFarkas wArgs p' q'

  let cs = pCs ++ p'Cs
  
  deriv <- proveExpr subTactic cf e p p'
  conclude R.Shift cf q q' cs e [deriv]  

proveTickDefer :: Prove PositionedExpr Derivation
proveTickDefer tactic cf e@(Tick c e1) q q' = do
  let [subTactic] = subTactics 1 tactic
  if isJust cf then do
    deriv <- proveExpr subTactic cf e1 q q'
    conclude R.TickDefer cf q q' [] e [deriv]
  else do
    p_ <- emptyAnnCtx (M.map _args q') "P" "" 
    (p, cs) <- ctxDefByPlus p_ q' (ConstTerm (fromMaybe 1 c))

    deriv <- proveExpr subTactic cf e1 q p

    conclude R.TickDefer cf q q' cs e [deriv]

removeRedundantVars :: Prove PositionedExpr Derivation -> Prove PositionedExpr Derivation
removeRedundantVars prove tactic cf e q q' = if (not . null) (redundentVars q e) then
  proveWeakenVar (Rule R.WeakenVar [tactic]) cf e q q'
  else prove tactic cf e q q'

proveExpr :: Prove PositionedExpr Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var []) cf e@(Var _) = removeRedundantVars proveVar tactic cf e
proveExpr tactic@(Rule R.Cmp []) cf e@(Const {}) | isCmp e = proveCmp tactic cf e
proveExpr tactic@(Rule R.Const []) cf e@(Const {}) = removeRedundantVars proveConst tactic cf e 
proveExpr tactic@(Rule R.Match _) cf e@(Match {}) = proveMatch tactic cf e
proveExpr tactic@(Rule R.Ite _) cf e@(Ite {}) = proveIte tactic cf e
proveExpr tactic@(Rule (R.Let _) _) cf e@(Let {}) = proveLet tactic cf e
proveExpr tactic@(Rule R.TickDefer _) cf e@(Tick {}) = removeRedundantVars proveTickDefer tactic cf e
proveExpr tactic@(Rule R.WeakenVar _) cf e = proveWeakenVar tactic cf e
proveExpr tactic@(Rule (R.Weaken _) _) cf e = proveWeaken tactic cf e
proveExpr tactic@(Rule R.Shift _) cf e = proveShift tactic cf e
proveExpr tactic@(Rule R.App _) cf e@(App id _) = removeRedundantVars proveApp tactic cf e
-- auto tactic
proveExpr Auto cf e = proveExpr (genTactic e) cf e 
proveExpr tactic _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"

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

proveFunBody :: Prove PositionedFunDef Derivation
proveFunBody _ cf (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic cf e q q'

proveFun :: PositionedFunDef -> ProveMonad Derivation
proveFun fun@(FunDef _ fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  
  -- prove both with and without costs for well-typedness
  let cfAnns = withoutCost ann
  derivsCf <- mapM (\(n, (p, p')) -> proveFunBody Auto (Just n) fun p p') $ zip [0..] cfAnns
  
  let (q, q') = withCost ann  
  deriv <- proveFunBody Auto Nothing fun q q'
  
  return $ T.Node (R.FunRuleApp fun) (deriv:derivsCf)
