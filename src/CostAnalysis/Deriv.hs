{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Deriv where

import qualified Data.List as L
import qualified Data.Tree as T
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set(Set)
import qualified Data.Text as Text
import Prelude hiding (or, and, negate, sum)

import Ast hiding (Coefficient, CostAnnotation(..))
import Constants (isBasicConst)
import Primitive(Id, applySubst, traceShow)
import Control.Monad.RWS

import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential hiding (Factor(..), emptyAnn, defaultAnn, defaultTempl, defaultNegAnn, enrichWithDefaults)
--import CostAnalysis.RsrcAnn hiding (fromAnn)
import CostAnalysis.Annotation hiding (sub)
import CostAnalysis.Predicate
import CostAnalysis.Template(FreeTemplate)
import qualified CostAnalysis.Template as Templ
import CostAnalysis.Constraint ( and,
                                 or,
                                 le,
                                 eq,
                                 sub,
                                 Constraint,
                                 Term(ConstTerm), geZero )
import CostAnalysis.Weakening
import CostAnalysis.ProveMonad
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe, mapMaybe, isJust, catMaybes)


import CostAnalysis.Coeff (coeffArgs, justVars)
  
type ProofResult = (Derivation, [Constraint], FreeSignature)

type Prove e a = Tactic -> Maybe Int -> e -> (FreeAnn, FreeAnn, Set Predicate) -> FreeAnn -> ProveMonad a

proveConst :: Prove PositionedExpr Derivation
proveConst _ cf e@Error (q, qe, preds) q' = do
  let cs = unifyAssertEq q q'
  conclude R.Const cf (q, qe, preds) q' cs e []
proveConst _ cf e@(Const "(,)" args) (q, qe, preds) q' = do
  let cs = unifyAssertEqBy q q' (varsByType args)
  conclude R.Const cf (q, qe, preds) q' cs e []
proveConst _ cf e@(Const "numLit" _) (q, qe, preds) q' = do
  let cs = unifyAssertEq q q'
  conclude R.Var cf (q, qe, preds) q' cs e []
proveConst _ cf e@(Const id _) (q, qe, preds) q' = do
  pots <- use potentials
  let t = getType e
  cs <- (unifyAssertEq (M.delete t q) (M.delete t q') ++)
    <$> if M.member t pots then
          return $ cConst (potForType t pots) e (q M.! t, qe M.! t) (q' M.! t)
        else errorFrom (SynExpr e) $ "Constructor '" ++ Text.unpack id ++ "' not supported, by selected potential function(s)."
  conclude R.Const cf (q, qe, preds) q' cs e []

proveConstBase :: Prove PositionedExpr Derivation
proveConstBase _ cf e (q, qe, preds) q' = do
  let cs = unifyAssertEq q q'
  conclude R.ConstBase cf (q, qe, preds) q' cs e []

proveVar :: Prove PositionedExpr Derivation
proveVar _ cf e@(Var id) (q, qe, preds) q' = do
  let cs = unifyAssertEq q q'
  conclude R.Var cf (q, qe, preds) q' cs e []

proveIte :: Prove PositionedExpr Derivation
proveIte tactic cf e@(Ite (Coin p) e1 e2) (q, qe, preds) q' = do
  let [t1, t2] = subTactics 2 tactic
  q1 <- enrichWithDefaults False "Q1" "" q
  q2 <- enrichWithDefaults False "Q2" "" q
  qe1 <- fromAnn "Q1" "" qe
  qe2 <- fromAnn "Q1" "" qe
  let cs = concat $ [unifyAssertEq q (add
                                      (scale q1 (ConstTerm p))
                                      (scale q2 (ConstTerm (1-p)))),
                     unifyAssertEq qe (add
                                       (scale qe1 (ConstTerm p))
                                       (scale qe2 (ConstTerm (1-p))))] 
  deriv1 <- proveExpr t1 cf e1 (q1, qe1, preds) q'
  deriv2 <- proveExpr t2 cf e2 (q2, qe2, preds) q'
  conclude R.Ite cf (q, qe, preds) q' cs e [deriv1, deriv2]
proveIte tactic cf e@(Ite condExp e1 e2) (q, qe, preds) q' = do
  let [t0, t1, t2] = subTactics 3 tactic
  q1 <- fromAnn "Q1" "ite cond" q
  q2 <- fromAnn "Q2" "ite body" q
  let cs = assertEq q (add q1 q2)

  let cond = predFromCondition condExp
  let preds1 = maybe preds (`S.insert` preds) cond
  let preds2 = maybe preds (\p -> negate p `S.insert` preds) cond

  condResult <- emptyAnn M.empty "0" "ite cond"
  derivCond <- proveExpr t0 cf condExp (q1, qe, preds) condResult
  deriv1 <- proveExpr t1 cf e1 (q2, qe, preds1) q'
  deriv2 <- proveExpr t2 cf e2 (q2, qe, preds2) q'
  conclude R.Ite cf (q, qe, preds) q' cs e [derivCond, deriv1, deriv2]

getVar :: Type -> (PositionedPatternVar, Int) -> Maybe Id
getVar t (v@(Id _ id), _) | matchesType (getType v) t = Just id
                          | otherwise = Nothing
getVar t (v@(WildcardVar _), wcId) | matchesType (getType v) t =
                                     Just . Text.pack $ ("?w" ++ show wcId)
                                   | otherwise = Nothing

proveMatchArm :: Id -> Prove PositionedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf arm@(MatchArm pat@(ConstPat _ "(,)" patVars) e) (q, qe, preds) q' = do
  let tsMatch = filter (`M.member` q) $ splitProdType (getType pat)
  let tMatch = head tsMatch
  let vars = mapMaybe (getVar tMatch) $ zip patVars [0..]
  let p = M.adjust (Templ.substArg matchVar (head vars)) tMatch q
  let cs = unifyAssertEq q p
  let preds' = excludeByVars preds (S.singleton matchVar)
  deriv <- proveExpr tactic cf e (p, qe, preds') q'
  return (cs, deriv)
proveMatchArm matchVar tactic cf 
  (MatchArm pat@(ConstPat _ id patVars) e) (q, qe, preds) q' = do
  let tMatch = getType pat
  let nonMatchAnns = M.delete tMatch q
  let matchAnn = q M.! tMatch
  pot <- potForType tMatch <$> use potentials
  let vars = mapMaybe (getVar tMatch) $ zip patVars [0..]
  let args' = L.delete matchVar (Templ.args matchAnn) `L.union` vars
  p_ <- emptyTempl tMatch "P" "match arm" args'
  let (p, cs) = cMatch pot matchAnn p_ matchVar vars
  tellCs cs
  let preds' = excludeByVars preds (S.singleton matchVar)
  deriv <- proveExpr tactic cf e (M.insert tMatch p nonMatchAnns, qe, preds') q'
  return (cs, deriv)

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


splitLetCtx :: PositionedExpr -> PositionedExpr -> FreeTemplate -> ([Id], [Id])
splitLetCtx e1 e2 q = 
  let qArgs = S.fromList $ Templ.args q
      varsE1 = freeVars e1
      argsE1 = qArgs `S.intersection` varsE1
      argsE2 = qArgs S.\\ varsE1 in
    (S.toList argsE1, S.toList argsE2)

isLeaf :: PositionedExpr -> Bool
isLeaf Leaf = True
isLeaf _ = False

proveLet :: Prove PositionedExpr Derivation
proveLet tactic@(Rule (R.Let letArgs) _) cf e@(Let x e1 e2) (q, qe, preds) q' = do
  pots <- use potentials
  let [t1, t2] = subTactics 2 tactic
  let argSplit = M.map (splitLetCtx e1 e2) q
  let (varsE1, varsE2) = M.foldr (\(xs, ys) (xss, yss) -> (xs ++ xss, ys ++ yss)) ([],[]) argSplit
  let preds1 = restrictByVars preds (S.fromList varsE1)
  let preds2 = restrictByVars preds (S.fromList varsE2)

  let tsBind = filter (`M.member` q) $ splitProdType $ getType e1
  tBind <- if null tsBind then
             return Nothing
           else if length tsBind == 1 then
                  return $ Just (head tsBind)
                else
                  errorFrom (SynExpr e) "Binding product type in let expression is only supported singleton potential bearing types."
  
  let nonBindingQ = case tBind of
        Just t -> M.delete t q
        Nothing -> q

  annPe <- fromAnn "PE" "let:base e1" qe
  let peCs = assertZero annPe
             
  annP_ <- emptyAnn (M.map fst argSplit) "P" "let:base e1"
  annR_ <- emptyAnn (M.map snd argSplit) "R" "let:base e2"
  -- base
  let (nonBindingAnnP, nonBindingCsP) = defineByWith annP_ nonBindingQ (\t idx p q -> geZero p ++ p `le` q)
  let (nonBindingAnnR, nonBindingCsR) = defineByWith annR_ nonBindingQ
        (\t idx r q -> r `eq` sub [q, (nonBindingAnnP M.! t) Templ.! idx])
  let nonBindingCs = nonBindingCsP ++ nonBindingCsR
  
  -- potential bind
  (annP', annP, annR, cs, cfDerivs) <- case tBind of
    Just t -> do
      let bindingQ = q M.! t
      potE1 <- potForType t <$> use potentials
      let (gamma, delta) = argSplit M.! t
      bindingP' <- defaultTempl t "P'"  "let e1" ["e1"]
        
      let rangeD = rangeA . ranges $ potE1
      let rangeE = if R.NegE `elem` letArgs then
            rangeBNeg . ranges $ potE1 else rangeB . ranges $ potE1
      
      let is = letCfIdxs potE1 (q M.! t) delta (rangeD, rangeE) x

      ps_ <- emptyArrayFromIdxs t is "P" gamma
      ps'_ <- emptyArrayFromIdxs t is "P'" ["e1"]

      r_ <-  emptyTempl t "R" "let:base e2" (x:delta)

      let (p, pCs) = Templ.defineByWith (annP_ M.! t) bindingQ (\idx p q -> geZero p ++ p `le` q)
      let (ps, ps', cfCs) | M.null ps_ = (ps_, ps'_, [])
                          | otherwise = cLetCf potE1 bindingQ ps_ ps'_ x (gamma, delta) is
      let (r, rCs) = Templ.chainDef [
            Templ.cLetBodyUni bindingQ p bindingP' x,
            cLetBodyMulti potE1 bindingQ ps' x is] r_ 
      let bindingAnnP' = M.insert t bindingP' M.empty
      let bindingAnnP = M.insert t p nonBindingAnnP
      let bindingAnnR = M.insert t r nonBindingAnnR
      let annPs = map (\p -> M.insert t p nonBindingAnnP) (Templ.elems ps)
      let annPes = replicate (length annPs) annPe
      let annPs' = map (\p -> M.fromList [(t, p)]) (Templ.elems ps')
      let cfPreds = replicate (length annPs) preds1

      cfDerivs <- zipWithM (proveExpr t1 (Just $ fromMaybe 0 cf) e1) (zip3 annPs annPes cfPreds) annPs'
      
      return (bindingAnnP', bindingAnnP, bindingAnnR,
               pCs ++ peCs ++ cfCs ++ rCs ++ nonBindingCs,
               cfDerivs)
      -- derivs
    Nothing -> return (M.empty,
                       nonBindingAnnP,
                       nonBindingAnnR,
                       nonBindingCs, [])

  
  deriv1 <- proveExpr t1 cf e1 (annP, annPe, preds1) annP'
  deriv2 <- proveExpr t2 cf e2 (annR, qe, preds1) q'

  conclude (R.Let letArgs) cf (q, qe, preds) q' cs e ([deriv1, deriv2] ++ cfDerivs)

proveApp :: Prove PositionedExpr Derivation
proveApp tactic Nothing e@(App id args) (q, qe, pred) q' = do
  fnSig <- use sig
  let cSig = withCost $ fnSig M.! id
  let cfSigs = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs = or $ concatMap (linCombOfSig cSig) cfSigs
  conclude R.App Nothing (q, qe, pred) q' cs e []
  where linCombOfSig ((p, pe), p') ((r, re), r') = concat
          [and $
           unifyAssertEqBy q (add p (scale r (ConstTerm k))) (varsByType args)
           ++ unifyAssertEqBy qe (add pe (scale re (ConstTerm k))) (M.map Templ.args qe)
           ++ unifyAssertEq q' (add p' (scale r' (ConstTerm k)))
          | k <- [0,1,2]]
proveApp tactic (Just cf) e@(App id args) (q, qe, pred) q' = do
  fnSig <- use sig
  let cfSigs = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs = or $ linCombOfSig ((q, qe), q') (cfSigs L.!! cf)

  conclude R.App (Just cf) (q, qe, pred) q' cs e []
  where linCombOfSig ((q, qe), q') ((p, pe), p') = concat
          [ and $
            unifyAssertEqBy q (scale p (ConstTerm k)) (varsByType args)
            ++ unifyAssertEqBy qe (scale pe (ConstTerm k)) (M.map Templ.args qe)
            ++ unifyAssertEq q' (scale p' (ConstTerm k))
          | k <- [0,1,2]]

redundentVars :: FreeAnn -> Expr a -> [(Id, Type)]
redundentVars qs e =
  [ (x, t)
  | (t, q) <- M.toAscList qs,
    x <- Templ.args q,
    not $ x `S.member` freeVars e]


proveWeakenVar :: Prove PositionedExpr Derivation
proveWeakenVar tactic cf e (q, qe, preds) q' = do
  let redundant = redundentVars q e
  (var, tVar) <- if null redundant then
                errorFrom (SynExpr e) "Could not find a redundant variable to eleminate with the (w:var) rule."
              else
                return $ head redundant
  let [t] = subTactics 1 tactic
  let redundantQ = q M.! tVar
  pot <- potForType tVar <$> use potentials
  
  r_ <- emptyTempl tVar "R" "weaken var" $ L.delete var (Templ.args redundantQ)
  let (r,rCs) = Templ.defineBy r_ redundantQ
  let cs = Templ.assertGeZero (Templ.sub redundantQ r)
  let annR = M.insert tVar r q
  let preds' = excludeByVars preds (S.singleton var)
  
  deriv <- proveExpr t cf e (annR, qe, preds') q'
  conclude R.WeakenVar cf (q, qe, preds) q' cs e [deriv]
  
proveWeaken :: Prove PositionedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) cf e (q, qe, preds) q' = do
  let [t] = subTactics 1 tactic
  let wArgs' = S.fromList wArgs
  let neg = R.Neg `S.member` wArgs'
  
  p <- enrichWithDefaults neg "P" "weaken" q
  -- p <= q
  pCs <-  annFarkas wArgs' preds p q
  
  p' <- enrichWithDefaults neg "P'" "weaken" q'
  -- q' <= p'
  p'Cs <-  annFarkas wArgs' S.empty q' p'
  
  deriv <- proveExpr t cf e (p, qe, preds) p'
  conclude (R.Weaken wArgs) cf (q, qe, preds) q' (pCs ++ p'Cs) e [deriv]

proveShiftTerm :: Prove PositionedExpr Derivation
proveShiftTerm tactic cf e (q, qe, preds) q' = do
  let [subTactic] = subTactics 1 tactic

  pe <- fromAnn "PE" "shift:term" qe
  p' <- fromAnn "P'" "shift:term" q'

  r <- fromAnn "R" "shift:term" q'
  
  let cs = unifyAssertEq pe (add qe r)
        ++ unifyAssertEq p' (add q' r)
        ++ assertGeZero r

  deriv <- proveExpr subTactic cf e (q, pe, preds) p'

  conclude R.ShiftTerm cf (q, qe, preds) q' cs e [deriv]

proveShiftConst :: Prove PositionedExpr Derivation
proveShiftConst tactic cf e q q' = do
  sCf <- strongCf <$> use fnConfig 
  if isJust cf && sCf
    then proveShiftConstMono tactic cf e q q'
    else proveShiftConstSimple tactic cf e q q'

proveShiftConstSimple :: Prove PositionedExpr Derivation
proveShiftConstSimple tactic cf e (q, qe, preds) q' = do
  let [subTactic] = subTactics 1 tactic

  k <- freshVar

  p_ <- emptyAnn (M.map Templ.args q) "P" "shift" 
  (ps, pCs) <- defineByMinus p_ q k
    

  p'_ <- emptyAnn (M.map Templ.args q') "P'" "shift"
  (ps', p'Cs) <- defineByMinus p'_ q' k

  let cs = pCs ++ p'Cs ++ geZero k
  
  deriv <- proveExpr subTactic cf e (ps, qe, preds) ps'
  conclude R.ShiftConst cf (q, qe, preds) q' cs e [deriv]
proveShiftConstMono tactic cf e (qs, qe, preds) qs' = do
  let [subTactic] = subTactics 1 tactic
  let wArgs = S.fromList [R.Mono]

  k <- freshVar
  
  ps_ <- enrichWithDefaults False "P" "shift" qs
  (ps, constShiftCsQ) <- defineByMinus ps_ qs k
  ps'_ <- enrichWithDefaults False "P'" "shift" qs'
  (ps', constShiftCsQ') <- defineByMinus ps'_ qs' k
  let constShiftCs = and (constShiftCsQ ++ constShiftCsQ')

  pots <- use potentials

  let monoShiftCs = catMaybes $
        [(do
             let p = ps M.! tq
             let p' = ps' M.! tq'
             shiftQP <- monoShift fn xs c potQ p q
             shiftQ'P' <- monoShift fn ys c potQ' p' q'
             idxFnQ <- monoFnCoeff potQ fn xs c
             idxFnQ' <- monoFnCoeff potQ' fn ys c
             let cs =
                   eq (q Templ.!? idxFnQ) (q' Templ.!? idxFnQ')
                   ++ eq (q Templ.!? oneCoeff potQ) (q' Templ.!? oneCoeff potQ')
                   ++ assertZero otherQs 
                   ++ assertZero (M.delete tq ps)
                   ++ assertZero otherQ's
                   ++ assertZero (M.delete tq' ps')
             return $ and (shiftQP ++ shiftQ'P' ++ cs))
        | let c = 1,
          fn <- [minBound..],
          (tq, q) <- M.assocs qs,
          let potQ = potForType tq pots, 
          let otherQs = M.delete tq qs,
          (tq', q') <- M.assocs qs',
          let potQ' = potForType tq' pots,
          let otherQ's = M.delete tq' qs',
          xs <- map coeffArgs $ filter justVars (Templ.mixes q),
          ys <- map coeffArgs $ filter justVars (Templ.mixes q')]
  let cs = or $ constShiftCs ++ concat monoShiftCs
  
  deriv <- proveExpr subTactic cf e (ps, qe, preds) ps'
  conclude R.ShiftConst cf (qs, qe, preds) qs' cs e [deriv]  

proveTickDefer :: Prove PositionedExpr Derivation
proveTickDefer tactic cf e@(Tick c e1) (q, qe, preds) q' = do
  let [subTactic] = subTactics 1 tactic
  if isJust cf then do
    deriv <- proveExpr subTactic cf e1 (q, qe, preds) q'
    conclude R.TickDefer cf (q, qe, preds) q' [] e [deriv]
  else do
    p_ <- emptyAnn (M.map Templ.args q') "P" "" 
    (p, cs) <- defineByPlus p_ q' (ConstTerm (fromMaybe 1 c))

    deriv <- proveExpr subTactic cf e1 (q, qe, preds) p

    conclude R.TickDefer cf (q, qe, preds) q' cs e [deriv]

removeRedundantVars :: Prove PositionedExpr Derivation -> Prove PositionedExpr Derivation
removeRedundantVars prove tactic cf e (q, qe, preds) q' = if (not . null) (redundentVars q e) then
  proveWeakenVar (Rule R.WeakenVar [tactic]) cf e (q, qe, preds) q'
  else prove tactic cf e (q, qe, preds) q'

proveExpr :: Prove PositionedExpr Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var []) cf e@(Var _) = removeRedundantVars proveVar tactic cf e
proveExpr tactic@(Rule R.ConstBase []) cf e@(Const {}) | isBasicConst e = removeRedundantVars proveConstBase tactic cf e
proveExpr tactic@(Rule R.Const []) cf e@(Const {}) = removeRedundantVars proveConst tactic cf e 
proveExpr tactic@(Rule R.Match _) cf e@(Match {}) = proveMatch tactic cf e
proveExpr tactic@(Rule R.Ite _) cf e@(Ite {}) = proveIte tactic cf e
proveExpr tactic@(Rule (R.Let _) _) cf e@(Let {}) = proveLet tactic cf e
proveExpr tactic@(Rule R.TickDefer _) cf e@(Tick {}) = removeRedundantVars proveTickDefer tactic cf e
proveExpr tactic@(Rule R.WeakenVar _) cf e = proveWeakenVar tactic cf e
proveExpr tactic@(Rule (R.Weaken _) _) cf e = proveWeaken tactic cf e
proveExpr tactic@(Rule R.ShiftTerm _) cf e = proveShiftTerm tactic cf e
proveExpr tactic@(Rule R.ShiftConst _) cf e = proveShiftConst tactic cf e
proveExpr tactic@(Rule R.App _) cf e@(App id _) = removeRedundantVars proveApp tactic cf e
-- auto tactic
proveExpr Auto cf e = \q q' -> do
  fnCfg <- use fnConfig
  proveExpr (genTactic fnCfg cf e) cf e q q'
proveExpr tactic _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"

genTactic :: FnConfig -> Maybe Int -> PositionedExpr -> Tactic
genTactic cfg cf e@(Var {}) = autoWeaken cfg cf e (Rule R.Var [])
genTactic _ _ e@(Const {}) | isBasicConst e = Rule R.ConstBase []
genTactic cfg cf e@(Const {}) = autoWeaken cfg cf e (Rule R.Const [])
genTactic cfg cf (Match _ arms) = Rule R.Match $ map (genTactic cfg cf . armExpr) arms
genTactic cfg cf e@(Ite (Coin _) e2 e3) = let t1 = genTactic cfg cf e2 
                                              t2 = genTactic cfg cf e3
                                              tactic = Rule R.Ite [t1, t2] in
  autoWeaken cfg cf e tactic
genTactic cfg cf e@(Ite e1 e2 e3) = let t1 = genTactic cfg cf e1 
                                        t2 = genTactic cfg cf e2 
                                        t3 = genTactic cfg cf e3
                                        tactic = Rule R.Ite [t1, t2, t3] in
  autoWeaken cfg cf e tactic
genTactic cfg cf e@(App {}) = autoWeaken cfg cf e $ Rule R.ShiftConst [Rule R.App []]
genTactic cfg cf e@(Let _ binding body) = let tBinding = genTactic cfg cf binding
                                              t1 = Rule R.ShiftTerm [tBinding]
                                              t2 = genTactic cfg cf body
                                              ctx = peCtx $ getAnn e 
                                              neg = S.member BindsAppOrTickRec ctx in
  autoWeaken cfg cf e $ Rule (R.Let [R.NegE | neg]) [t1, t2]
genTactic cfg cf (Tick _ e) = Rule R.TickDefer [genTactic cfg cf e]
genTactic _ _ e = error $ "genTactic: " ++ printExprHead e

autoWeaken :: FnConfig -> Maybe Int -> PositionedExpr -> Tactic -> Tactic
autoWeaken cfg cf e tactic = case wArgsForExpr cfg e (isJust cf)  of
  [] -> tactic
  wArgs -> Rule (R.Weaken wArgs) [tactic]

wArgsForExpr :: FnConfig -> PositionedExpr -> Bool -> [R.WeakenArg]
wArgsForExpr cfg e cf = S.toList $ foldr checkCtx S.empty (wArgMap cf cfg)
  where ctx = peCtx $ getAnn e
        checkCtx (flags, impliedArgs) wArgs = if all (`S.member` ctx) flags then
          S.union wArgs (S.fromList impliedArgs) else wArgs

wArgMap :: Bool -> FnConfig -> [([ExprCtx], [R.WeakenArg])]
wArgMap cf@False _ =
  [ ([PseudoLeaf], [R.Mono]),
    ([BindsAppOrTickRec], [R.Neg]),
    ([BindsAppOrTick], [R.Mono, R.L2xy]),
    ([FirstAfterApp, OutermostLet], [R.L2xy, R.Mono]),
    ([FirstAfterMatch], [R.Mono]),
    ([IteCoin], [R.L2xy])]
wArgMap cf@True cfg | strongCf cfg =
                      [([FirstAfterMatch], [R.Mono])]
                    | otherwise = []

proveFunBody :: Prove PositionedFunDef Derivation
proveFunBody _ cf (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  fnConfig .= tfFnConfig ann
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic cf e q q'

proveFun :: PositionedFunDef -> ProveMonad Derivation
proveFun fun@(FunDef _ fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  
  -- prove both with and without costs for well-typedness
  let cfAnns = withoutCost ann
  derivsCf <- mapM (\(n, ((p, pe), p')) -> proveFunBody Auto (Just n) fun (p, pe, S.empty) p') $ zip [0..] cfAnns
  
  let ((q, qe), q') = withCost ann  
  deriv <- proveFunBody Auto Nothing fun (q, qe, S.empty) q'
  
  return $ T.Node (R.FunRuleApp fun) (deriv:derivsCf)
