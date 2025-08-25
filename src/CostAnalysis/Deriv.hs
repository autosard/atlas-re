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
import Primitive(Id, traceShow, traceShowV)
import Control.Monad.RWS

import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential hiding (Factor(..), emptyAnn, defaultAnn, defaultTempl, enrichWithDefaults)
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
                                 Constraint (Bot),
                                 Term(ConstTerm), geZero, iff )
import CostAnalysis.Weakening
import CostAnalysis.ProveMonad
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe, mapMaybe, catMaybes)


import CostAnalysis.Coeff (coeffArgs, justVars, CoeffIdx (Pure))
import CostAnalysis.Potential.Kind (fromKind)
import Control.Monad (when, unless)
import CostAnalysis.ProveMonad (defaultAnn)
import Control.Monad.Extra (ifM)
  
type ProofResult = (Derivation, [Constraint], FreeSignature)

type Prove e a = Tactic -> JudgementType -> ProveKind -> e -> (FreeAnn, FreeAnn, Set Predicate) -> FreeAnn -> ProveMonad a

proveConst :: Prove PositionedExpr Derivation
proveConst _ judgeType kind e@Error (q, qe, preds) q' = do
  let cs = unifyAssertEq q q' ++ assertZero qe
  conclude R.Const judgeType kind (q, qe, preds) q' cs e []
proveConst _ judgeType kind e@(Const "(,)" args) (q, qe, preds) q' = do
  let cs = unifyAssertEqBy q q' (varsByType args) ++ assertZero qe
  conclude R.Const judgeType kind (q, qe, preds) q' cs e []
proveConst _ judgeType kind e@(Const "numLit" _) (q, qe, preds) q' = do
  let cs = unifyAssertEq q q' ++ assertZero qe
  conclude R.Var judgeType kind (q, qe, preds) q' cs e []
proveConst _ judgeType kind e@(Const id _) (q, qe, preds) q' = do
  pots <- use potentials
  
  let t = getType e
  csT <- if M.member t pots then do
          pot <- potForType t 
          return $ cConst pot e preds (q M.! t, qe M.! t) (q' M.! t)
        else errorFrom (SynExpr e) $ "Constructor '" ++ Text.unpack id ++ "' not supported, by selected potential function(s)."
  let cs = assertZero qe
           ++ unifyAssertEq (M.delete t q) (M.delete t q')
           ++ csT
  conclude R.Const judgeType kind (q, qe, preds) q' cs e []

proveConstUnfold :: Prove PositionedExpr Derivation
proveConstUnfold tactic judgeType kind e@(Const _ _) (q, qe, preds) q' = do
  let [t1] = subTactics 1 tactic
  p <- fromAnn "P" "unfold" q
  r <- fromAnn "R" "unfold" q

  void <- fromAnn "PE" "unfold" qe
  let cs = assertZero void
           ++ assertEq r (add p q)
  derivUnfold <- proveConst (Rule R.Const []) judgeType kind e (p, void , preds) qe
  derivMain <- proveExpr t1 judgeType kind e (r, void , preds) q'
  conclude R.ConstUnfold judgeType kind (q, qe, preds) q' cs e [derivUnfold, derivMain]
  
proveConstBase :: Prove PositionedExpr Derivation
proveConstBase _ judgeType kind e (q, qe, preds) q' = do
  let cs = unifyAssertEq q q' ++ assertZero qe
  conclude R.ConstBase judgeType kind (q, qe, preds) q' cs e []

proveVar :: Prove PositionedExpr Derivation
proveVar _ judgeType kind e@(Var id) (q, qe, preds) q' = do
  let cs = unifyAssertEq q q' ++ assertZero qe
  conclude R.Var judgeType kind (q, qe, preds) q' cs e []

proveIte :: Prove PositionedExpr Derivation
proveIte tactic judgeType kind e@(Ite (Coin p) e1 e2) (q, qe, preds) q' = do
  let [t1, t2] = subTactics 2 tactic
  q1 <- enrichWithDefaults Templ.defaultTemplOpts "Q1" "" q
  q2 <- enrichWithDefaults Templ.defaultTemplOpts "Q2" "" q
  qe1 <- fromAnn "Q1" "" qe
  qe2 <- fromAnn "Q1" "" qe
  let cs = concat $ [unifyAssertEq q (add
                                      (scale q1 (ConstTerm p))
                                      (scale q2 (ConstTerm (1-p)))),
                     unifyAssertEq qe (add
                                       (scale qe1 (ConstTerm p))
                                       (scale qe2 (ConstTerm (1-p))))] 
  deriv1 <- proveExpr t1 judgeType kind e1 (q1, qe1, preds) q'
  deriv2 <- proveExpr t2 judgeType kind e2 (q2, qe2, preds) q'
  conclude R.Ite judgeType kind (q, qe, preds) q' cs e [deriv1, deriv2]
proveIte tactic judgeType kind e@(Ite condExp e1 e2) (q, qe, preds) q' = do
  let [t0, t1, t2] = subTactics 3 tactic
  q1 <- fromAnn "Q1" "ite cond" q
  q1e <- fromAnn "Q1E" "ite cond" qe
  q2 <- fromAnn "Q2" "ite body" q
  let cs = assertEq q (add q1 q2) ++ assertZero q1e

  let cond = predFromCondition condExp
  let preds1 = maybe preds (`S.insert` preds) cond
  let preds2 = maybe preds (\p -> negate p `S.insert` preds) cond

  condResult <- emptyAnn M.empty "0" "ite cond"
  derivCond <- proveExpr t0 judgeType kind condExp (q1, q1e, preds) condResult
  deriv1 <- proveExpr t1 judgeType kind e1 (q2, qe, preds1) q'
  deriv2 <- proveExpr t2 judgeType kind e2 (q2, qe, preds2) q'
  conclude R.Ite judgeType kind (q, qe, preds) q' cs e [derivCond, deriv1, deriv2]

getVar :: Type -> (PositionedPatternVar, Int) -> Maybe Id
getVar t (v@(Id _ id), _) | matchesType (getType v) t = Just id
                          | otherwise = Nothing
getVar t (v@(WildcardVar _), wcId) | matchesType (getType v) t =
                                     Just . Text.pack $ ("?w" ++ show wcId)
                                   | otherwise = Nothing

proveMatchArm :: Id -> Prove PositionedMatchArm ([Constraint], [Derivation])
proveMatchArm matchVar tactic judgeType kind arm@(MatchArm pat@(ConstPat _ "(,)" patVars) e) (q, qe, preds) q' = do
  let tsMatch = filter (`M.member` q) $ splitProdType (getType pat)
  let tMatch = head tsMatch
  let vars = mapMaybe (getVar tMatch) $ zip patVars [0..]
  let p = M.adjust (Templ.substArg matchVar (head vars)) tMatch q
  let cs = unifyAssertEq q p
  let preds' = excludeByVars preds (S.singleton matchVar)
  deriv <- proveExpr tactic judgeType kind e (p, qe, preds') q'
  return (cs, [deriv])
proveMatchArm matchVar tactic judgeType kind
  (MatchArm pat@(ConstPat _ id patVars) e) (q, qe, preds) q' = do
  let tMatch = getType pat
  let nonMatchAnns = M.delete tMatch q
  let matchAnn = q M.! tMatch
  pot <- potForType tMatch 
  let vars = mapMaybe (getVar tMatch) $ zip patVars [0..]
  let args' = L.delete matchVar (Templ.args matchAnn) `L.union` vars

  let cases = constCases pot pat
  (ps, cs)  <- case cases of
    [] -> constrainCase pot tMatch matchAnn args' vars Nothing
    cases -> foldr accum ([],[]) <$>
      mapM (constrainCase pot tMatch matchAnn args' vars . Just) cases
  let preds' = excludeByVars preds (S.singleton matchVar)
  derivs <- mapM (\(p, casePred) -> proveExpr tactic judgeType kind e (M.insert tMatch p nonMatchAnns, qe, maybe preds' (`S.insert` preds') casePred) q') $
    zip ps (toMaybeList ps cases)
  return (cs, derivs)
  where toMaybeList :: [a] -> [Predicate] -> [Maybe Predicate]
        toMaybeList xs [] = map (const Nothing) xs
        toMaybeList _ ps = map Just ps
        constrainCase :: Potential
                         -> Type
                         -> FreeTemplate
                         -> [Id]
                         -> [Id]
                         -> Maybe Predicate
                         -> ProveMonad ([FreeTemplate], [Constraint])
        constrainCase pot t q args vars _case = do
          p_ <- emptyTempl "P" "match arm" args (Templ.ghosts q)
          let (p, cs) = cMatch pot q p_ _case matchVar vars
          return ([p], cs)
        accum :: ([FreeTemplate], [Constraint]) -> ([FreeTemplate], [Constraint]) -> ([FreeTemplate], [Constraint])
        accum (p, cs) (ps, css) = (p ++ ps, cs ++ css)

proveMatchArm matchVar tactic judgeType kind arm@(MatchArm pat@(Alias _ x) e) q q' = do
    deriv <- proveExpr tactic judgeType kind e q q'
    return ([], [deriv])
proveMatchArm _ _ _ _ arm _ _ = errorFrom (SynArm arm) "unsupported pattern match in rule (match)."

proveMatch :: Prove PositionedExpr Derivation
proveMatch tactic judgeType kind e@(Match (Var x) arms) q q' = do
  let tactics = subTactics (length arms) tactic
  results <- zipWithM proveArmWithTactic tactics arms
  let (cs, derivs) = foldr accum ([], []) results
  conclude R.Match judgeType kind q q' cs e derivs
  
  where accum (cs, derivs) (css, derivss) = (cs ++ css, derivs ++ derivss)
        proveArmWithTactic tactic arm = proveMatchArm x tactic judgeType kind arm q q'


splitLetCtx :: PositionedExpr -> PositionedExpr -> FreeTemplate -> ([Id], [Id], [Id])
splitLetCtx e1 e2 q = 
  let qArgs = S.fromList $ Templ.args q
      varsE1 = freeVars e1
      argsE1 = qArgs `S.intersection` varsE1
      argsE2 = qArgs S.\\ varsE1
      gVars = S.fromList $ Templ.ghosts q in
    (S.toList (argsE1 `S.union` (qArgs `S.intersection` gVars)),
     S.toList argsE2,
     S.toList gVars)

proveLet :: Prove PositionedExpr Derivation
proveLet tactic@(Rule (R.Let letArgs) _) judgeType kind e@(Let x e1 e2) (q, qe, preds) q' = do
  pots <- use potentials
  let [t1, t2] = subTactics 2 tactic
  let argSplit = M.map (splitLetCtx e1 e2) q
  let gammaDelta = M.map (\(g,d,_) -> (g,d)) argSplit
  let (varsE1, varsE2) = M.foldr (\(xs, ys) (xss, yss) -> (xs ++ xss, ys ++ yss)) ([],[]) gammaDelta
  let preds1 = restrictByVars preds (S.fromList varsE1)
  let preds2 = restrictByVars preds (S.fromList varsE2)
  let mixedPreds = (preds S.\\ preds1) S.\\ preds2
  (mixedPreds', predDerivs, predCs) <- extendPredicates mixedPreds varsE1 x t1 e1 
  
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
             
  annP_ <- emptyAnn (M.map (\(args, _, ghosts) -> (args, ghosts))  argSplit) "P" "let:base e1"
  annR_ <- emptyAnn (M.map (\(_, args, ghosts) -> (args, ghosts)) argSplit) "R" "let:base e2"
  -- base
  let (nonBindingAnnP, nonBindingCsP) = defineByWith annP_ nonBindingQ (\t idx p q -> geZero p ++ p `le` q)
  let (nonBindingAnnR, nonBindingCsR) = defineByWith annR_ nonBindingQ
        (\t idx r q -> r `eq` sub [q, (nonBindingAnnP M.! t) Templ.! idx])
  let gammaDelta = M.map (\(g,d,_) -> (g,d)) argSplit
  let nonBindingCs = nonBindingCsP ++ nonBindingCsR ++ nonBindingMultiZero nonBindingQ gammaDelta      
  -- let nonBindingCs = nonBindingCsP ++ nonBindingCsR ++ nonBindingMultiGeZero nonBindingQ argSplit
  
  -- potential bind
  (annP', annP, annR, cs, cfDerivs) <- case tBind of
    Just t -> do
      let bindingQ = q M.! t
      potE1 <- potForType t 
      let (gamma, delta, gVars) = argSplit M.! t
      bindingP' <- defaultTempl t "P'"  "let e1" (Templ.args (q' M.! t))
      --["e1"]
        
      
      let templOpts = Templ.defaultTemplOpts {Templ.negBindingConst=R.NegE `elem` letArgs}
      
      let is = letCfIdxs potE1 (q M.! t) delta templOpts x

      ps_ <- emptyArrayFromIdxs x is "P" gamma gVars
      ps'_ <- emptyArrayFromIdxs x is "P'" (Templ.args (q' M.! t)) gVars

      r_ <-  emptyTempl "R" "let:base e2" (x:delta) gVars

      let (p, pCs) = Templ.defineByWith (annP_ M.! t) bindingQ (\idx p q -> geZero p ++ p `le` q)
      let (ps, ps', cfCs) | M.null ps_ = (ps_, ps'_, [])
                          | otherwise = cLetCf potE1 bindingQ ps_ ps'_ x (gamma, delta) (map snd is)
      let (r, rCs) = Templ.chainDef [
            Templ.cLetBodyUni bindingQ p bindingP' x,
            cLetBodyMulti potE1 bindingQ ps' x (map snd is)] r_ 
      let bindingAnnP' = M.insert t bindingP' M.empty
      let bindingAnnP = M.insert t p nonBindingAnnP
      let bindingAnnR = M.insert t r nonBindingAnnR
      let annPs = map (\p -> M.insert t p nonBindingAnnP) (Templ.elems ps)
      let annPes = replicate (length annPs) annPe
      let annPs' = map (\p -> M.fromList [(t, p)]) (Templ.elems ps')
      let cfPreds = replicate (length annPs) preds1

--      cfDerivs <- zipWithM (proveExpr t1 (Cf $ fromMaybe 0 (cfSigIdx judgeType)) kind e1) (zip3 annPs annPes cfPreds) annPs'
      cfDerivs <- mapM
        (\(p, p', j@(judgeT, _)) -> case judgeT of
            (Cf _) -> proveExpr t1 CfAny kind e1 p p'
            CfAny -> proveExpr t1 CfAny kind e1 p p'
            Aux m -> proveExpr t1 (Aux m) kind e1 p p')
        $ zip3 (zip3 annPs annPes cfPreds) annPs' is
      
      return (bindingAnnP', bindingAnnP, bindingAnnR,
               pCs ++ peCs ++ cfCs ++ rCs ++ nonBindingCs,
               cfDerivs)
      -- derivs
    Nothing -> return (M.empty,
                       nonBindingAnnP,
                       nonBindingAnnR,
                       nonBindingCs, [])

  
  deriv1 <- proveExpr t1 judgeType kind e1 (annP, annPe, preds1) annP'
  deriv2 <- proveExpr t2 judgeType kind e2 (annR, qe, preds2 `S.union` S.fromList mixedPreds') q'

  conclude (R.Let letArgs) judgeType kind (q, qe, preds) q' (cs ++ predCs) e ([deriv1, deriv2] ++ cfDerivs ++ predDerivs)
--  conclude (R.Let letArgs) judgeType (q, qe, preds) q' cs e ([deriv1, deriv2] ++ cfDerivs)

extendPredicates :: Set Predicate
  -> [Id]
  -> Id
  -> Tactic
  -> PositionedExpr
  -> ProveMonad ([Predicate], [Derivation], [Constraint])
extendPredicates preds gammaVars bindVar tactic e = do
  foldM accum ([],[],[]) preds
  where go (Predicate m op x y pre t) = do
          let pot = fromKind . potForMeasure $ m
          p <- freshAtom
          let (pred', kind) = if x `L.elem` gammaVars 
                              then (Predicate m op bindVar y [p] t, Upper)
                              else (Predicate m op x bindVar [p] t, Lower)
          q <- singleAnn pot t (M.singleton t gammaVars) "P" "let preds"
          qe <- defaultAnn (M.singleton t ["e1"]) "PE" "let preds"
          q' <- singleAnn pot t (M.singleton t ["e1"]) "P'" "let preds"
          let cs = iff [p] $ and (pre ++ 
                assertZeroExcept q t [Pure x, Pure y]
                ++ assertZeroExcept q' t [Pure "e1"])
                ++ assertZero qe
          deriv <- proveExpr tactic (Aux m) kind e (q, qe, S.empty) q'
          return (pred', deriv, cs)
        accum a@(preds, derivs, css) pred = 
          if noAuxSigs pred then
            return a
          else do
            (pred, deriv, cs) <- go pred
            return (pred:preds, deriv:derivs, cs ++ css)

noAuxSigs :: Predicate -> Bool
noAuxSigs (Predicate m _ _ _ _ _) = 
  let pot = fromKind . potForMeasure $ m in
    null (auxSigs pot)
  

proveApp :: Prove PositionedExpr Derivation
proveApp tactic Standard kind e@(App id args) (q, qe, pred) q' = do
  fnSig <- use sig
  let cSig = withCost $ fnSig M.! id
  let cfSigs = withoutCost $ fnSig M.! id
  let cs = or $ concatMap (linCombOfSig (varsByType args) appScale ((q, qe), q') cSig) cfSigs
  conclude R.App Standard kind (q, qe, pred) q' cs e []
proveApp tactic (Cf cf) kind e@(App id args) (q, qe, pred) q' = do
  fnSig <- use sig
  let cfSigs = withoutCost $ fnSig M.! id
  zero <- emptyAnn M.empty "0" "app cf zero"
  let sigZero = FunSig (zero, zero) zero
  let cs = or $ linCombOfSig (orderArgsForCall q args) appScale ((q, qe), q') sigZero (cfSigs L.!! cf)
  conclude R.App (Cf cf) kind (q, qe, pred) q' cs e []
proveApp tactic CfAny kind e@(App id args) (q, qe, pred) q' = do
  fnSig <- use sig
  let cfSigs = withoutCost $ fnSig M.! id
  zero <- emptyAnn M.empty "0" "app cf zero"
  let sigZero = FunSig (zero, zero) zero
  let cs = or $ concatMap (linCombOfSig (orderArgsForCall q args) appScale ((q, qe), q') sigZero) cfSigs
  conclude R.App CfAny kind (q, qe, pred) q' cs e []  
proveApp tactic (Aux measure) kind e@(App id args) (q, qe, pred) q' = do
  fnSig <- use sig
  let auxSigs = aux $ fnSig M.! id
  zero <- emptyAnn M.empty "0" "app cf zero"
  let sigZero = FunSig (zero, zero) zero
  let cs = or $ linCombOfSig (varsByType args) appScale ((q, qe), q') sigZero (auxSigs M.! (measure, kind))
  conclude R.App (Aux measure) kind (q, qe, pred) q' cs e []

orderArgsForCall :: FreeAnn -> [PositionedExpr] -> M.Map Type [Id]
orderArgsForCall q callArgs = let orderedArgs = varsByType callArgs in
  M.mapWithKey (\t a -> (Templ.args a L.\\ (orderedArgs M.! t)) ++ orderedArgs M.! t) q

appScale :: [Rational]
appScale = [0,1,2]

linCombOfSig args rangeK ((q, qe), q') (FunSig (p, pe) p') (FunSig (r, re) r')
  = concat
  [ and $
    unifyAssertEqBy q (add p (scale r (ConstTerm k))) args
--    ++ unifyAssertEqBy qe (add p (scale re (ConstTerm k))) (M.map Templ.args qe)
    ++ unifyAssertEq q' (add p' (scale r' (ConstTerm k)))
  | k <- rangeK] 

redundentVars :: FreeAnn -> FreeAnn -> Expr a -> [(Id, Type)]
redundentVars qs q' e = let ghostVars = annArgs Templ.ghosts qs in
  [ (x, t)
  | (t, q) <- M.toAscList qs,
    x <- Templ.args q,
    not $ x `S.member` freeVars e,
    x `L.notElem` ghostVars,
    x `L.notElem` annArgs Templ.args q']
  where annArgs :: (FreeTemplate -> [Id]) -> FreeAnn -> [Id]
        annArgs getArgs qs = foldr (\q acc -> acc ++ getArgs q) [] (M.elems qs)


proveWeakenVar :: Prove PositionedExpr Derivation
proveWeakenVar tactic judgeType kind e (q, qe, preds) q' = do
  let redundant = redundentVars q q' e
  (var, tVar) <- if null redundant then
                errorFrom (SynExpr e) "Could not find a redundant variable to eleminate with the (w:var) rule."
              else
                return $ head redundant
  let [t] = subTactics 1 tactic
  let redundantQ = q M.! tVar
  pot <- potForType tVar 
  
  r_ <- emptyTempl "R" "weaken var" (L.delete var (Templ.args redundantQ)) (Templ.ghosts redundantQ)
  let (r,rCs) = Templ.defineBy r_ redundantQ
  let cs = rCs ++ Templ.assertGeZero (Templ.sub redundantQ r)
  let annR = M.insert tVar r q
  let preds' = excludeByVars preds (S.singleton var)
  
  deriv <- proveExpr t judgeType kind e (annR, qe, preds') q'
  conclude R.WeakenVar judgeType kind (q, qe, preds) q' cs e [deriv]
  
proveWeaken :: Prove PositionedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) judgeType kind e (q, qe, preds) q' = do
  let [t] = subTactics 1 tactic
  let wArgs' = S.fromList wArgs
  let templOpts = Templ.defaultTemplOpts {Templ.negBindingConst=R.Neg `S.member` wArgs'}
  
  p <- enrichWithDefaults templOpts "P" "weaken" q
  p' <- enrichWithDefaults templOpts "P'" "weaken" q'

  (pCs, p'Cs) <- case kind of
    Upper -> (,) <$>
      -- p <= q
      annFarkas wArgs' preds p q
      -- q' <= p'
      <*> annFarkas wArgs' S.empty q' p'
    Lower -> (,) <$>
      -- q <= p
      annFarkas wArgs' preds q p
      -- p' <= q'
      <*> annFarkas wArgs' S.empty p' q'
  
  deriv <- proveExpr t judgeType kind e (p, qe, preds) p'
  conclude (R.Weaken wArgs) judgeType kind (q, qe, preds) q' (pCs ++ p'Cs) e [deriv]

proveShiftTerm :: Prove PositionedExpr Derivation
proveShiftTerm tactic judgeType kind e (q, qe, preds) q' = do
  let [subTactic] = subTactics 1 tactic

  pe <- fromAnn "PE" "shift:term" qe
  p' <- fromAnn "P'" "shift:term" q'

  r <- fromAnn "R" "shift:term" q'
  
  let cs = unifyAssertEq (add qe r) pe
        ++ unifyAssertEq p' (add q' r)
        ++ assertGeZero r

  deriv <- proveExpr subTactic judgeType kind e (q, pe, preds) p'

  conclude R.ShiftTerm judgeType kind (q, qe, preds) q' cs e [deriv]

proveShiftConst :: Prove PositionedExpr Derivation
proveShiftConst tactic judgeType kind e q q' = do
  sCf <- strongCf <$> use fnConfig 
  if isCostFree judgeType && sCf
    then proveShiftConstMono tactic judgeType kind e q q'
    else proveShiftConstSimple tactic judgeType kind e q q'

proveShiftConstSimple :: Prove PositionedExpr Derivation
proveShiftConstSimple tactic judgeType kind e (q, qe, preds) q' = do
  let [subTactic] = subTactics 1 tactic

  k <- freshVar

  p_ <- emptyAnnFrom q "P" "shift" 
  (ps, pCs) <- defineByMinus p_ q k
    

  p'_ <- emptyAnnFrom q' "P'" "shift"
  (ps', p'Cs) <- defineByMinus p'_ q' k

  let cs = pCs ++ p'Cs ++ geZero k
  
  deriv <- proveExpr subTactic judgeType kind e (ps, qe, preds) ps'
  conclude R.ShiftConst judgeType kind (q, qe, preds) q' cs e [deriv]
proveShiftConstMono tactic judgeType kind e (qs, qe, preds) qs' = do
  let [subTactic] = subTactics 1 tactic
  let wArgs = S.fromList [R.Mono]

  k <- freshVar
  
  ps_ <- enrichWithDefaults Templ.defaultTemplOpts "P" "shift" qs
  (ps, constShiftCsQ) <- defineByMinus ps_ qs k
  ps'_ <- enrichWithDefaults Templ.defaultTemplOpts "P'" "shift" qs'
  (ps', constShiftCsQ') <- defineByMinus ps'_ qs' k
  let constShiftCs = and (constShiftCsQ ++ constShiftCsQ')

  pots <- M.fromList <$> mapM (\t -> do p <- potForType t
                                        return (t, p)) (M.keys qs)

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
          let potQ = pots M.! tq, 
          let otherQs = M.delete tq qs,
          (tq', q') <- M.assocs qs',
          let potQ' = pots M.! tq',
          let otherQ's = M.delete tq' qs',
          xs <- map coeffArgs $ filter justVars (Templ.mixes q),
          ys <- map coeffArgs $ filter justVars (Templ.mixes q')]
  let cs = or $ constShiftCs ++ concat monoShiftCs
  
  deriv <- proveExpr subTactic judgeType kind e (ps, qe, preds) ps'
  conclude R.ShiftConst judgeType kind (qs, qe, preds) qs' cs e [deriv]  

proveTickDefer :: Prove PositionedExpr Derivation
proveTickDefer tactic judgeType kind e@(Tick c e1) (q, qe, preds) q' = do
  let [subTactic] = subTactics 1 tactic
  if isCostFree judgeType then do
    deriv <- proveExpr subTactic judgeType kind e1 (q, qe, preds) q'
    conclude R.TickDefer judgeType kind (q, qe, preds) q' [] e [deriv]
  else do
    p_ <- emptyAnnFrom q' "P" "" 
    (p, cs) <- defineByPlus p_ q' (ConstTerm (fromMaybe 1 c))

    deriv <- proveExpr subTactic judgeType kind e1 (q, qe, preds) p

    conclude R.TickDefer judgeType kind (q, qe, preds) q' cs e [deriv]

removeRedundantVars :: Prove PositionedExpr Derivation -> Prove PositionedExpr Derivation
removeRedundantVars prove tactic judgeType kind e (q, qe, preds) q' = if (not . null) (redundentVars q q' e) then
  proveWeakenVar (Rule R.WeakenVar [tactic]) judgeType kind e (q, qe, preds) q'
  else prove tactic judgeType kind e (q, qe, preds) q'

proveExpr :: Prove PositionedExpr Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var []) judgeType kind e@(Var _) = removeRedundantVars proveVar tactic judgeType kind e
proveExpr tactic@(Rule R.ConstBase []) judgeType kind e@(Const {}) | isBasicConst e = removeRedundantVars proveConstBase tactic judgeType kind e
proveExpr tactic@(Rule R.Const []) judgeType kind e@(Const {}) = removeRedundantVars proveConst tactic judgeType kind e
proveExpr tactic@(Rule R.ConstUnfold _) judgeType kind e@(Const {}) = proveConstUnfold tactic judgeType kind e
proveExpr tactic@(Rule R.Match _) judgeType kind e@(Match {}) = proveMatch tactic judgeType kind e 
proveExpr tactic@(Rule R.Ite _) judgeType kind e@(Ite {}) = proveIte tactic judgeType kind e 
proveExpr tactic@(Rule (R.Let _) _) judgeType kind e@(Let {}) = proveLet tactic judgeType kind e 
proveExpr tactic@(Rule R.TickDefer _) judgeType kind e@(Tick {}) = removeRedundantVars proveTickDefer tactic judgeType kind e
proveExpr tactic@(Rule R.WeakenVar _) judgeType kind e = proveWeakenVar tactic judgeType kind e 
proveExpr tactic@(Rule (R.Weaken _) _) judgeType kind e = proveWeaken tactic judgeType kind e
proveExpr tactic@(Rule R.ShiftTerm _) judgeType kind e = proveShiftTerm tactic judgeType kind e
proveExpr tactic@(Rule R.ShiftConst _) judgeType kind e = proveShiftConst tactic judgeType kind e
proveExpr tactic@(Rule R.App _) judgeType kind e@(App id _) = removeRedundantVars proveApp tactic judgeType' kind e
  where recursive = S.member RecCall (peCtx . getAnn $ e)
        judgeType' = case judgeType of
                       (Cf n) -> if recursive
                         then Cf n
                         else CfAny
                       jt -> jt
        
-- auto tactic
proveExpr Auto judgeType kind e = \q q' -> do
  fnCfg <- use fnConfig
  rhs <- view rhsTerms
  proveExpr (genTactic fnCfg rhs judgeType e) judgeType kind e q q'
proveExpr tactic _ _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"

genTactic :: FnConfig -> Bool -> JudgementType -> PositionedExpr -> Tactic
genTactic cfg rhsTerms judgeType e@(Var {}) = autoWeaken cfg judgeType e (Rule R.Var [])
genTactic _ rhsTerms _ e@(Const {}) | isBasicConst e = Rule R.ConstBase []
genTactic cfg rhsTerms judgeType e@(Const {}) = if rhsTerms
  then Rule R.ConstUnfold [autoWeaken cfg judgeType e (Rule R.Const [])]
  else autoWeaken cfg judgeType e (Rule R.Const [])
genTactic cfg rhsTerms judgeType (Match _ arms) = Rule R.Match $
  map (genTactic cfg rhsTerms judgeType . armExpr) arms
genTactic cfg rhsTerms judgeType e@(Ite (Coin _) e2 e3) =
  let t1 = genTactic cfg rhsTerms judgeType e2 
      t2 = genTactic cfg rhsTerms judgeType e3
      tactic = Rule R.Ite [t1, t2] in
  autoWeaken cfg judgeType e tactic
genTactic cfg rhsTerms judgeType e@(Ite e1 e2 e3) =
  let t1 = genTactic cfg rhsTerms judgeType e1 
      t2 = genTactic cfg rhsTerms judgeType e2 
      t3 = genTactic cfg rhsTerms judgeType e3
      tactic = Rule R.Ite [t1, t2, t3] in
  autoWeaken cfg judgeType e tactic
genTactic cfg rhsTerms judgeType e@(App {}) = autoWeaken cfg judgeType e $
  Rule R.ShiftConst [Rule R.App []]
genTactic cfg rhsTerms judgeType e@(Let _ binding body) =
  let tBinding = genTactic cfg rhsTerms judgeType binding
      t1 = tBinding
      t2 = genTactic cfg rhsTerms judgeType body
      ctx = peCtx $ getAnn e 
      neg = S.member BindsAppOrTickRec ctx in
  autoWeaken cfg judgeType e $ Rule (R.Let [R.NegE | neg]) [t1, t2]
genTactic cfg rhsTerms judgeType (Tick _ e) =
  Rule R.TickDefer [genTactic cfg rhsTerms judgeType e]
genTactic _ _ _ e = error $ "genTactic: " ++ printExprHead e 

autoWeaken :: FnConfig -> JudgementType -> PositionedExpr -> Tactic -> Tactic
autoWeaken cfg judgeType e tactic = case wArgsForExpr cfg e judgeType of
  [] -> tactic
  wArgs -> Rule (R.Weaken wArgs) [tactic]

wArgsForExpr :: FnConfig -> PositionedExpr -> JudgementType -> [R.WeakenArg]
wArgsForExpr cfg e judgeType = S.toList $ foldr checkCtx S.empty (wArgMap judgeType cfg)
  where ctx = peCtx $ getAnn e
        checkCtx (flags, impliedArgs) wArgs = if all (`S.member` ctx) flags then
          S.union wArgs (S.fromList impliedArgs) else wArgs

wArgMap :: JudgementType -> FnConfig -> [([ExprCtx], [R.WeakenArg])]
wArgMap Standard _ =
  [ ([PseudoLeaf], [R.Mono]),
    ([BindsAppOrTickRec], [R.Neg]),
    ([BindsAppOrTick], [R.Mono, R.L2xy]),
    ([FirstAfterApp, OutermostLet], [R.L2xy, R.Mono]),
    ([FirstAfterMatch], [R.Mono]),
    ([IteCoin], [R.L2xy])]
wArgMap judgeT cfg | strongCf cfg || isAux judgeT =
                  [([FirstAfterMatch], [R.Mono])]
              | otherwise = []
  where isAux (Aux _) = True
        isAux _ = False

proveFunBody :: Prove PositionedFunDef Derivation
proveFunBody _ cf kind (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  fnConfig .= tfFnConfig ann
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic cf kind e q q'

proveFun :: PositionedFunDef -> ProveMonad Derivation
proveFun fun@(FunDef _ fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  
  -- prove both with and without costs for well-typedness
  let cfAnns = withoutCost ann
  let auxAnns = aux ann
  derivsCf <- mapM (\(n, FunSig (p, pe) p') ->
                      proveFunBody Auto (Cf n) Upper fun (instGhostVars p, pe, S.empty) (instGhostVars p'))
              $ zip [0..] cfAnns
  
  
  let (FunSig (q, qe) q') = withCost ann  
  deriv <- proveFunBody Auto Standard Upper fun (q, qe, S.empty) q'
  
  auxMode .= True
  derivsAux <- mapM (\((measure, kind), FunSig (a, ae) a') -> proveFunBody Auto (Aux measure) kind fun (a, ae, S.empty) a') $ M.assocs auxAnns
  auxMode .= False
  
  return $ T.Node (R.FunRuleApp fun) (deriv:derivsCf ++ derivsAux)
--  return $ T.Node (R.FunRuleApp fun) (derivsCf ++ derivsAux)
