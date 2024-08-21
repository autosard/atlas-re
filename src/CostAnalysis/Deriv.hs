{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}


module CostAnalysis.Deriv where


import qualified Data.Tree as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Text as Text
import Prelude hiding (or)

import Ast hiding (Coefficient)
import Primitive(Id)
import Control.Monad.RWS
import Control.Monad.Except ( runExceptT )
import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential hiding (Factor(..), emptyAnn, defaultAnn, defaultNegAnn, enrichWithDefaults)
import CostAnalysis.RsrcAnn hiding (fromAnn)
import CostAnalysis.Constraint ( ge,
                                 le,
                                 eq,
                                 or,
                                 Constraint,
                                 Term(ConstTerm) )
import CostAnalysis.Weakening
import CostAnalysis.ProveMonad
import StaticAnalysis(freeVars, calledFunctions')
import Data.Maybe (fromMaybe, mapMaybe, maybeToList)
import SourceError

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x
  
type ProofResult = (Derivation, [Constraint], RsrcSignature)

runProof :: Bool -> TypedModule -> Potential -> Map Id Tactic
  -> (Int, Either SourceError ProofResult)
runProof ignoreAnns mod pot tactics = (state' ^. varIdGen, (,cs, state' ^. sig) <$> deriv)
  where (deriv, state', cs) = runRWS rws env state
        rws = runExceptT $ proveModule mod ignoreAnns
        env = ProofEnv pot tactics
        state = ProofState M.empty 0 0 Nothing

genFunRsrcAnn :: TypedFunDef -> ProveMonad FunRsrcAnn
genFunRsrcAnn fun = do
  let (ctxFrom, argTo) = ctxFromFn fun
  let argsFrom = M.toAscList ctxFrom
  from <- defaultAnn "Q" "fn" argsFrom
  to <- defaultAnn "Q'" "fn" [argTo]
  fromCf <- defaultAnn "P" "fn cf" argsFrom
  toCf <- defaultAnn "P'" "fn cf" [argTo]
  return $ FunRsrcAnn (from, to) (fromCf, toCf)


type TypeCtx = Map Id Type

type Prove e a = Tactic -> Bool -> TypeCtx -> e -> RsrcAnn -> RsrcAnn -> ProveMonad a

proveConst :: Prove TypedExpr Derivation
proveConst _ cf ctx e q q' = do
  pot <- view potential
  let cs = cConst pot q q'
  conclude R.Const cf q q' cs e []

proveCmp :: Prove TypedExpr Derivation
proveCmp _ cf _ e q q' = do
  unless (isBool $ getType e) $
    errorFrom (SynExpr e) "(cmp) applied to non-boolean expression."
  let cs = annEq q q'
  conclude R.Cmp cf q q' cs e []

proveVar :: Prove TypedExpr Derivation
proveVar _ cf ctx e@(Var id) q q' = do
  --when (length ctx /= 1) $ errorFrom (SynExpr e) "(var) applied to non-singleton context."
  when (M.notMember id ctx) $ errorFrom (SynExpr e) $ "(var) applied for variable '" ++ Text.unpack id ++ "' that is not in the context."
  let cs = annLikeUnify q q'
  conclude R.Var cf q q' cs e []

provePair :: Prove TypedExpr Derivation
provePair _ cf ctx e@(Tuple (Var x1) (Var x2)) q q' = do
  when (isTree (ctx M.!x1) && isTree (ctx M.!x2)) $
    errorFrom (SynExpr e) "(pair) applied to more then one tree type."
  let cs = annEq q q'
  conclude R.Const cf q q' cs e []

proveIte :: Prove TypedExpr Derivation
proveIte tactic cf ctx e@(Ite (Var x) e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  let ctx' = M.delete x ctx
  deriv1 <- proveExpr t1 cf ctx' e1 q q'
  deriv2 <- proveExpr t2 cf ctx' e2 q q'
  conclude R.Ite cf q q' [] e [deriv1, deriv2]

proveMatchArm :: Id -> Prove TypedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf ctx
  arm@(MatchArm (PatTuple _ (Id _ x1) (Id _ x2)) e) q q' = do
  let (tx1, tx2) = splitTupleType $ getType arm
  when (isTree tx1 && isTree tx2) $
    errorFrom (SynArm arm) "(match) applied to a pair with more then one tree type."
    
  let ctx' = ctx `M.union` M.fromList [(x1, tx1), (x2, tx2)]
  deriv <- proveExpr tactic cf ctx' e q q'
  return ([], deriv)
proveMatchArm matchVar tactic cf ctx
  (MatchArm pat@(ConstPat _ id patVars) e) q q' = do
  pot <- view potential
  let tMatch = getType pat
  let vars = mapMaybe getVar patVars
  let ctx' = M.delete matchVar ctx `M.union` M.fromList vars
  p_ <- emptyAnn "P" "match arm" (M.toAscList ctx')
  let (p, cs) = cMatch pot q p_ matchVar vars
  tell cs
  deriv <- proveExpr tactic cf ctx' e p q'
  return (cs, deriv)
  where getVar v@(Id _ id) = Just (id, getType v)
        getVar (WildcardVar _) = Nothing
proveMatchArm matchVar tactic cf ctx arm@(MatchArm pat@(Alias _ x) e) q q' = do
  if M.member x ctx then do
    deriv <- proveExpr tactic cf ctx e q q'
    return ([], deriv)
  else errorFrom (SynArm arm) "found invalid alias (variable not previously defined) in match arm."
proveMatchArm _ _ _ _ arm _ _ = errorFrom (SynArm arm) "unsupported pattern match in rule (match)."

proveMatch :: Prove TypedExpr Derivation
proveMatch tactic cf ctx e@(Match (Var x) arms) q q' = do
  pot <- view potential
  let tactics = subTactics (length arms) tactic
  results <- zipWithM proveArmWithTactic tactics arms
  let (cs, derivs) = foldr accum ([], []) results
  conclude R.Match cf q q' cs e derivs
  
  where accum (cs, deriv) (css, derivs) = (cs ++ css, deriv:derivs)
        proveArmWithTactic tactic arm = proveMatchArm x tactic cf ctx arm q q'


splitLetCtx :: TypeCtx -> TypedExpr -> TypedExpr -> ProveMonad (TypeCtx, TypeCtx)
splitLetCtx ctx e1 e2 = do
  let varsE1 = freeVars e1
  let ctxE1 = M.restrictKeys ctx varsE1
  let ctxE2 = ctx M.\\ ctxE1
  return (ctxE1, ctxE2)

isRecursive :: TypedExpr -> ProveMonad Bool
isRecursive e = do
  use currentFn >>= \case
    Just (FunDef _ fn _ _) -> return $ S.member fn (calledFunctions' e)
   
proveLet :: Prove TypedExpr Derivation
proveLet tactic@(Rule (R.Let letArgs) _) cf ctx e@(Let x e1 e2) q q'
  -- let
  | isTree $ getType e1 = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2
      let (gamma, delta) = (M.toAscList ctxE1, M.toAscList ctxE2)
      let ctxE2' = M.insert x (getType e1) ctxE2 
      -- TODO if let binds a recursive call then use negative numbers for e
      -- neg <- isRecursive e1
      let neg = R.NegE `elem` letArgs 

      p_ <- emptyAnn "P" "let:base e1" gamma
      p' <- defaultAnn  "P'"  "let:base e1" [("e", getType e1)]
      r_ <- emptyAnn "R" "let:base e2" (M.toAscList ctxE2')
      
      let rangeD = rangeA . ranges $ pot
      let rangeE = if neg then rangeBNeg . ranges $ pot else rangeB . ranges $ pot
      
      let bdes = forAllCombinations q (M.keys ctxE2) (rangeD, rangeE) x
      
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
  | otherwise = do
      pot <- view potential
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

proveApp :: Prove TypedExpr Derivation
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

redundentVars :: RsrcAnn -> TypedExpr -> Set Id
redundentVars q e = S.fromList (annVars q) S.\\ freeVars e

proveWeakenVar :: Prove TypedExpr Derivation
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
  
proveWeaken :: Prove TypedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) cf ctx e q q' = do
  pot <- view potential
  let [t] = subTactics 1 tactic
  let wArgs' = S.fromList wArgs
  
  p <- enrichWithDefaults "P" "" q
  -- p <= q
  pCs <-  farkas pot wArgs' (p^.coeffs) p q
  
  p' <- enrichWithDefaults "P'" "" q'
  -- q' <= p'
  p'Cs <-  farkas pot wArgs' (p'^.coeffs) q' p'
  
  deriv <- proveExpr t cf ctx e p p'
  conclude (R.Weaken wArgs) cf q q' (pCs ++ p'Cs) e [deriv]

proveShift :: Prove TypedExpr Derivation
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

proveTickDefer :: Prove TypedExpr Derivation
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

removeRedundantVars :: Prove TypedExpr Derivation -> Prove TypedExpr Derivation
removeRedundantVars prove tactic cf ctx e q q' = if (not . null) (redundentVars q e) then
  proveWeakenVar (Rule R.WeakenVar [tactic]) cf ctx e q q'
  else prove tactic cf ctx e q q'

proveExpr :: Prove TypedExpr Derivation
-- manual tactic
proveExpr tactic@(Rule R.Var []) cf ctx e@(Var _) = removeRedundantVars proveVar tactic cf ctx e
proveExpr tactic@(Rule R.Cmp []) cf ctx e@(Const {}) | isCmp e = proveCmp tactic cf ctx e
proveExpr tactic@(Rule R.Const []) cf ctx e@(Tuple {}) = removeRedundantVars provePair tactic cf ctx e

proveExpr tactic@(Rule R.Const []) cf ctx e@(Const {}) = removeRedundantVars proveConst tactic cf ctx e 
proveExpr tactic@(Rule R.Match _) cf ctx e@(Match {}) = proveMatch tactic cf ctx e
proveExpr tactic@(Rule R.Ite _) cf ctx e@(Ite {}) = proveIte tactic cf ctx e
proveExpr tactic@(Rule (R.Let _) _) cf ctx e@(Let {}) = proveLet tactic cf ctx e
proveExpr tactic@(Rule R.TickDefer _) cf ctx e = removeRedundantVars proveTickDefer tactic cf ctx e
proveExpr tactic@(Rule R.WeakenVar _) cf ctx e = proveWeakenVar tactic cf ctx e
proveExpr tactic@(Rule (R.Weaken _) _) cf ctx e = proveWeaken tactic cf ctx e
proveExpr tactic@(Rule R.Shift _) cf ctx e = proveShift tactic cf ctx e
proveExpr tactic@(Rule R.App _) cf ctx e@(App {}) = removeRedundantVars proveApp tactic cf ctx e
-- auto tactic
-- proveExpr Auto cf ctx e@Leaf = proveWeaken (Rule (R.Weaken []) [Auto]) cf ctx e
-- proveExpr Auto cf ctx e@(Var _) = proveVar Auto cf ctx e
-- proveExpr Auto cf ctx e@(Const _ _) | isCmp e = proveCmp Auto cf ctx e
-- proveExpr Auto cf ctx e@(Node {}) = proveNode Auto cf ctx e
-- proveExpr Auto cf ctx e@(Match _ _) = proveMatch Auto cf ctx e

proveExpr tactic _ _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"


ctxFromProdType :: Type -> [Id] -> TypeCtx
ctxFromProdType (TAp Prod ts) args = M.fromList $ zip args ts
ctxFromProdType t _ = error $ "Cannot construct a type context from the non product type '" ++ show t ++ "'."

proveFun :: Prove TypedFunDef Derivation
proveFun _ cf _ (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  let ctx = ctxFromProdType tFrom args
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic cf ctx e q q'

proveFunWithAnn :: Bool -> TypedFunDef  -> FunRsrcAnn -> ProveMonad Derivation
proveFunWithAnn ignoreAnns fun@(FunDef funAnn _ _ _) ann  = do
  currentFn .= Just fun
  
  -- prove both with and without costs for well-typedness
  let (p, p') = withoutCost ann
  derivCf <- proveFun Auto True M.empty fun p p'
  
  let (q, q') = withCost ann  
  deriv <- proveFun Auto False M.empty fun q q'

  unless ignoreAnns (do
    tell . concat . maybeToList $ (annLe q . fst <$> tfRsrcWithCost funAnn)
    tell . concat . maybeToList $ (annLe q' . snd <$> tfRsrcWithCost funAnn)
    tell . concat . maybeToList $ (annLe p . fst <$> tfRsrcWithoutCost funAnn)
    tell . concat . maybeToList $ (annLe p' . snd <$> tfRsrcWithoutCost funAnn))
  
  return $ T.Node (R.FunRuleApp fun) [derivCf, deriv]

setRightSidesEqual :: [FunRsrcAnn] -> [Constraint]
setRightSidesEqual [] = []
setRightSidesEqual (ann:anns) = concat [annEq (snd . withCost $ ann) (snd . withCost $ ann')
                                       | ann' <- anns]

proveModule :: TypedModule -> Bool -> ProveMonad Derivation
proveModule mod ignoreAnns = do
  s <- use sig
  funAnns <- mapM (\f@(Fn name _ _) -> (name,) <$> genFunRsrcAnn f) mod
  tell $ setRightSidesEqual (map snd funAnns)
  sig .= s `M.union` M.fromList funAnns
  derivs <- mapM (uncurry (proveFunWithAnn ignoreAnns)) $ zipWith (\x y -> (x, snd y)) mod funAnns
  return $ T.Node (R.ProgRuleApp mod) derivs
