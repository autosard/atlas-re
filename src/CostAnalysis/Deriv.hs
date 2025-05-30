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
import Constants (isBasicConst)
import Primitive(Id)
import Control.Monad.RWS

import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential hiding (Factor(..), emptyAnn, defaultAnn, defaultTempl, defaultNegAnn, enrichWithDefaults)
--import CostAnalysis.RsrcAnn hiding (fromAnn)
import CostAnalysis.Annotation hiding (sub)
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

import Debug.Trace hiding (traceShow)
import CostAnalysis.Coeff (coeffArgs, justVars)

traceShow x = trace (show x) x
  
type ProofResult = (Derivation, [Constraint], FreeSignature)

type Prove e a = Tactic -> Maybe Int -> e -> (FreeAnn, FreeAnn) -> FreeAnn -> ProveMonad a

proveConst :: Prove PositionedExpr Derivation
proveConst _ cf e@Error (q, qe) q' = do
  let cs = unifyAssertEq q q'
  conclude R.Const cf (q, qe) q' cs e []
proveConst _ cf e@(Const "(,)" args) (q, qe) q' = do
  let cs = unifyAssertEqBy q q' (varsByType args)
  conclude R.Const cf (q, qe) q' cs e []
proveConst _ cf e@(Const "numLit" _) (q, qe) q' = do
  let cs = unifyAssertEq q q'
  conclude R.Var cf (q, qe) q' cs e []
proveConst _ cf e@(Const id _) (q, qe) q' = do
  pots <- use potentials
  let t = getType e
  cs <- (unifyAssertEq (M.delete t q) (M.delete t q') ++)
    <$> if M.member t pots then
          return $ cConst (potForType t pots) e (q M.! t, qe M.! t) (q' M.! t)
        else errorFrom (SynExpr e) $ "Constructor '" ++ Text.unpack id ++ "' not supported, by selected potential function(s)."
  conclude R.Const cf (q, qe) q' cs e []

proveConstBase :: Prove PositionedExpr Derivation
proveConstBase _ cf e (q, qe) q' = do
  let cs = unifyAssertEq q q'
  conclude R.ConstBase cf (q, qe) q' cs e []

proveVar :: Prove PositionedExpr Derivation
proveVar _ cf e@(Var id) (q, qe) q' = do
  let cs = unifyAssertEq q q'
  conclude R.Var cf (q, qe) q' cs e []

proveIte :: Prove PositionedExpr Derivation
proveIte tactic cf e@(Ite (Coin p) e1 e2) (q, qe) q' = do
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
  deriv1 <- proveExpr t1 cf e1 (q1, qe1) q'
  deriv2 <- proveExpr t2 cf e2 (q2, qe2) q'
  conclude R.Ite cf (q, qe) q' cs e [deriv1, deriv2]
proveIte tactic cf e@(Ite _ e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  deriv1 <- proveExpr t1 cf e1 q q'
  deriv2 <- proveExpr t2 cf e2 q q'
  conclude R.Ite cf q q' [] e [deriv1, deriv2]

getVar :: Type -> (PositionedPatternVar, Int) -> Maybe Id
getVar t (v@(Id _ id), _) | matchesType (getType v) t = Just id
                          | otherwise = Nothing
getVar t (v@(WildcardVar _), wcId) | matchesType (getType v) t =
                                     Just . Text.pack $ ("?w" ++ show wcId)
                                   | otherwise = Nothing

proveMatchArm :: Id -> Prove PositionedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf arm@(MatchArm pat@(ConstPat _ "(,)" patVars) e) (q, qe) q' = do
  let tsMatch = filter (`M.member` q) $ splitProdType (getType pat)
  let tMatch = head tsMatch
  let vars = mapMaybe (getVar tMatch) $ zip patVars [0..]
  let p = M.adjust (Templ.substArg matchVar (head vars)) tMatch q
  let cs = unifyAssertEq q p
  deriv <- proveExpr tactic cf e (p, qe) q'
  return (cs, deriv)
proveMatchArm matchVar tactic cf 
  (MatchArm pat@(ConstPat _ id patVars) e) (q, qe) q' = do
  let tMatch = getType pat
  let nonMatchAnns = M.delete tMatch q
  let matchAnn = q M.! tMatch
  pot <- potForType tMatch <$> use potentials
  let vars = mapMaybe (getVar tMatch) $ zip patVars [0..]
  let args' = L.delete matchVar (Templ.args matchAnn) `L.union` vars
  p_ <- emptyTempl tMatch "P" "match arm" args'
  let (p, cs) = cMatch pot matchAnn p_ matchVar vars
  tellCs cs
  deriv <- proveExpr tactic cf e (M.insert tMatch p nonMatchAnns, qe) q'
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
proveLet tactic@(Rule (R.Let letArgs) _) cf e@(Let x e1 e2) (q, qe) q' = do
  pots <- use potentials
  let [t1, t2] = subTactics 2 tactic
  let argSplit = M.map (splitLetCtx e1 e2) q

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
      let (ps, ps', cfCs) = cLetCf potE1 bindingQ ps_ ps'_ x (gamma, delta) is
      let (r, rCs) = Templ.chainDef [
            Templ.cLetBodyUni bindingQ p bindingP' x,
            cLetBodyMulti potE1 bindingQ ps' x is] r_ 
      let bindingAnnP' = M.insert t bindingP' M.empty
      let bindingAnnP = M.insert t p nonBindingAnnP
      let bindingAnnR = M.insert t r nonBindingAnnR
      let annPs = map (\p -> M.insert t p nonBindingAnnP) (Templ.elems ps)
      let annPes = replicate (length annPs) annPe
      let annPs' = map (\p -> M.fromList [(t, p)]) (Templ.elems ps')

      cfDerivs <- zipWithM (proveExpr t1 (Just $ fromMaybe 0 cf) e1) (zip annPs annPes) annPs'
      
      return (bindingAnnP', bindingAnnP, bindingAnnR,
               pCs ++ peCs ++ cfCs ++ rCs ++ nonBindingCs,
               cfDerivs)
      -- derivs
    Nothing -> return (M.empty,
                       nonBindingAnnP,
                       nonBindingAnnR,
                       nonBindingCs, [])

  
  deriv1 <- proveExpr t1 cf e1 (annP, annPe) annP'
  deriv2 <- proveExpr t2 cf e2 (annR, qe) q'

  conclude (R.Let letArgs) cf (q, qe) q' cs e ([deriv1, deriv2] ++ cfDerivs)

proveApp :: Prove PositionedExpr Derivation
proveApp tactic Nothing e@(App id args) (q, qe) q' = do
  fnSig <- use sig
  let cSig = withCost $ fnSig M.! id
  let cfSigs = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs = or $ concatMap (linCombOfSig cSig) cfSigs
  conclude R.App Nothing (q, qe) q' cs e []
  where linCombOfSig ((p, pe), p') ((r, re), r') = concat
          [and $
           unifyAssertEqBy q (add p (scale r (ConstTerm k))) (varsByType args)
           ++ unifyAssertEqBy qe (add pe (scale re (ConstTerm k))) (M.map Templ.args qe)
           ++ unifyAssertEq q' (add p' (scale r' (ConstTerm k)))
          | k <- [0,1,2]]
proveApp tactic (Just cf) e@(App id args) (q, qe) q' = do
  fnSig <- use sig
  let cfSigs = withoutCost $ fnSig M.! id
  k <- freshVar
  let cs = or $ linCombOfSig ((q, qe), q') (cfSigs L.!! cf)

  conclude R.App (Just cf) (q, qe) q' cs e []
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
proveWeakenVar tactic cf e (q, qe) q' = do
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
  
  deriv <- proveExpr t cf e (annR, qe) q'
  conclude R.WeakenVar cf (q, qe) q' cs e [deriv]
  
proveWeaken :: Prove PositionedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) cf e (q, qe) q' = do
  let [t] = subTactics 1 tactic
  let wArgs' = S.fromList wArgs
  let neg = R.Neg `S.member` wArgs'
  
  p <- enrichWithDefaults neg "P" "weaken" q
  -- p <= q
  pCs <-  annFarkas wArgs' p q
  
  p' <- enrichWithDefaults neg "P'" "weaken" q'
  -- q' <= p'
  p'Cs <-  annFarkas wArgs' q' p'
  
  deriv <- proveExpr t cf e (p, qe) p'
  conclude (R.Weaken wArgs) cf (q, qe) q' (pCs ++ p'Cs) e [deriv]

proveShiftTerm :: Prove PositionedExpr Derivation
proveShiftTerm tactic cf e (q, qe) q' = do
  let [subTactic] = subTactics 1 tactic

  pe <- fromAnn "PE" "shift:term" qe
  p' <- fromAnn "P'" "shift:term" q'

  r <- fromAnn "R" "shift:term" q'
  

  let cs = unifyAssertEq pe (add qe r)
        ++ unifyAssertEq p' (add q' r)
        ++ assertGeZero r

  deriv <- proveExpr subTactic cf e (q, pe) p'

  conclude R.ShiftTerm cf (q, qe) q' cs e [deriv]
  

proveShiftConst :: Prove PositionedExpr Derivation
proveShiftConst tactic cf@Nothing e (q, qe) q' = do
  let [subTactic] = subTactics 1 tactic

  k <- freshVar

  p_ <- emptyAnn (M.map Templ.args q) "P" "shift" 
  (ps, pCs) <- defineByMinus p_ q k
    

  p'_ <- emptyAnn (M.map Templ.args q') "P'" "shift"
  (ps', p'Cs) <- defineByMinus p'_ q' k

  let cs = pCs ++ p'Cs ++ geZero k
  
  deriv <- proveExpr subTactic cf e (ps, qe) ps'
  conclude R.ShiftConst cf (q, qe) q' cs e [deriv]
proveShiftConst tactic cf@(Just _) e (qs, qe) qs' = do
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
  
  deriv <- proveExpr subTactic cf e (ps, qe) ps'
  conclude R.ShiftConst cf (qs, qe) qs' cs e [deriv]  

proveTickDefer :: Prove PositionedExpr Derivation
proveTickDefer tactic cf e@(Tick c e1) (q, qe) q' = do
  let [subTactic] = subTactics 1 tactic
  if isJust cf then do
    deriv <- proveExpr subTactic cf e1 (q, qe) q'
    conclude R.TickDefer cf (q, qe) q' [] e [deriv]
  else do
    p_ <- emptyAnn (M.map Templ.args q') "P" "" 
    (p, cs) <- defineByPlus p_ q' (ConstTerm (fromMaybe 1 c))

    deriv <- proveExpr subTactic cf e1 (q, qe) p

    conclude R.TickDefer cf (q, qe) q' cs e [deriv]

removeRedundantVars :: Prove PositionedExpr Derivation -> Prove PositionedExpr Derivation
removeRedundantVars prove tactic cf e (q, qe) q' = if (not . null) (redundentVars q e) then
  proveWeakenVar (Rule R.WeakenVar [tactic]) cf e (q, qe) q'
  else prove tactic cf e (q, qe) q'

proveExpr :: Prove PositionedExpr Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var []) cf e@(Var _) = removeRedundantVars proveVar tactic cf e
proveExpr tactic@(Rule R.ConstBase []) cf e@(Const {}) | isBasicConst e = proveConstBase tactic cf e
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
proveExpr Auto cf e = proveExpr (genTactic cf e) cf e 
proveExpr tactic _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"

genTactic :: Maybe Int -> PositionedExpr -> Tactic
genTactic cf e@(Var {}) = autoWeaken cf e (Rule R.Var [])
genTactic _ e@(Const {}) | isBasicConst e = Rule R.ConstBase []
genTactic cf e@(Const {}) = autoWeaken cf e (Rule R.Const [])
genTactic cf (Match _ arms) = Rule R.Match $ map (genTactic cf . armExpr) arms
genTactic cf e@(Ite _ e2 e3) = let t1 = genTactic cf e2 
                                   t2 = genTactic cf e3 in
  autoWeaken cf e $ Rule R.Ite [t1, t2]
genTactic _ (App {}) = Rule R.ShiftConst [Rule R.App []]
genTactic cf e@(Let _ binding body) = let tBinding = genTactic cf binding
                                          t1 = Rule R.ShiftTerm [tBinding]
                                          --t1 = tBinding
                                          t2 = genTactic cf body
                                          ctx = peCtx $ getAnn e 
                                          neg = S.member BindsAppOrTickRec ctx in
  autoWeaken cf e $ Rule (R.Let [R.NegE | neg]) [t1, t2]
genTactic cf (Tick _ e) = Rule R.TickDefer [genTactic cf e]
genTactic _ e = error $ "genTactic: " ++ printExprHead e

autoWeaken :: Maybe Int -> PositionedExpr -> Tactic -> Tactic
autoWeaken (Just _) _ tactic = tactic -- no weakening for cf
autoWeaken _ e tactic = case wArgsForExpr e of
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
