{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module CostAnalysis.Deriv where

import Data.Tree(Tree)
import qualified Data.Tree as T
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Text(Text)

import Ast hiding (Coefficient)
import Primitive(Id)
import Control.Monad.RWS
import Control.Monad.Except
import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential hiding (Factor(..))
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe, mapMaybe)
import SourceError

import Debug.Trace (trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

data RuleApp = RuleApp R.Rule [Constraint] TypedExpr

type Derivation = Tree RuleApp

data ProofState a = ProofState {
  _sig :: RsrcSignature a,
  _annIdGen :: Int
  }
  deriving (Show)

makeLenses ''ProofState

data ProofEnv a = ProofEnv {
  _potential :: Potential a,
  _tactics :: Map Id Tactic
  }

makeLenses ''ProofEnv


type ProveMonad p a = ExceptT SourceError (RWS (ProofEnv p) [Constraint] (ProofState p)) a

type ProofResult a = ([Derivation], [Constraint], RsrcSignature a)

runProof :: HasCoeffs a => TypedModule -> Potential a -> Map Id Tactic
  -> Either SourceError (ProofResult a)
runProof mod pot tactics = (,cs, state' ^. sig) <$> deriv
  where (deriv, state', cs) = runRWS rws env state
        rws = runExceptT $ proveModule mod
        env = ProofEnv pot tactics
        state = ProofState M.empty 0

genAnnIds :: Int -> ProveMonad a [Int]
genAnnIds n = do
  g <- use annIdGen
  annIdGen .= g+n
  return [g..(g+n-1)]

genAnnIdPair :: ProveMonad a (Int, Int)
genAnnIdPair = do
  g <- use annIdGen
  annIdGen .= g+2
  return (g, g+1)

genAnnId :: ProveMonad a Int
genAnnId = do
  g <- use annIdGen
  annIdGen .= g+1
  return g

forAllCombinations' :: Bool -> [Id] -> Id -> Text -> [Id] -> ProveMonad a (AnnArray (RsrcAnn a))
forAllCombinations' neg xs x label ys = do
  pot <- view potential
  g <- use annIdGen
  let (array, g') = forAllCombinations pot neg xs x g label ys
  annIdGen .= g'
  return array

genFunRsrcAnn :: TypedFunDef -> ProveMonad a (FunRsrcAnn a)
genFunRsrcAnn fun = do
  pot <- view potential
  let (ctxFrom, (argTo, tTo)) = ctxFromFn fun
  (fromId, toId) <- genAnnIdPair
  let argsFrom = M.keys (M.filter isTree ctxFrom)
  let argsTo = [argTo | isTree tTo]
  let from = rsrcAnn pot fromId "Q" argsFrom
  let to = rsrcAnn pot toId "Q'" argsTo
  (fromIdCf, toIdCf) <- genAnnIdPair
  let fromCf = rsrcAnn pot fromId "P" argsFrom
  let toCf = rsrcAnn pot toId "P'" argsTo
  return $ FunRsrcAnn (from, to) (fromCf, toCf)


type TypeCtx = Map Id Type

type Prove e a = forall p. HasCoeffs p => Tactic -> Bool -> TypeCtx -> e -> RsrcAnn p -> RsrcAnn p -> ProveMonad p a

errorFrom :: Syntax Typed -> String -> ProveMonad p a
errorFrom e msg = throwError $ SourceError loc msg
  where loc = case (teSrc . getAnn) e of
          (Loc pos) -> pos
          (DerivedFrom pos) -> pos

proveConst :: Prove TypedExpr Derivation
proveConst _ _ ctx e q q' = do
  p <- view potential
  let cs = cEq p q q'
  tell cs
  return $ T.Node (RuleApp R.Const cs e) []

proveCmp :: Prove TypedExpr Derivation
proveCmp _ _ _ e _ _ = do
  if not . isBool $ getType e then
    errorFrom (SynExpr e) "cmp rule applied to non-boolean expression."
  else return $ T.Node (RuleApp R.Cmp [] e) []

proveVar :: Prove TypedExpr Derivation
proveVar _ _ _ e _ _ = return $ T.Node (RuleApp R.Var [] e) []

provePair :: Prove TypedExpr Derivation
provePair _ _ ctx e@(Tuple (Var x1) (Var x2)) q q' = do
  if not $ isTree (ctx M.!x1) && isTree (ctx M.!x2) then do
    pot <- view potential
    let cs = cEq pot q q'
    tell cs
    return $ T.Node (RuleApp R.Const [] e) []
  else errorFrom (SynExpr e) "pair rule applied to more then one tree type."

proveIte :: Prove TypedExpr Derivation
proveIte tactic cf ctx e@(Ite _ e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  deriv1 <- proveExpr t1 cf ctx e1 q q'
  deriv2 <- proveExpr t2 cf ctx e2 q q'
  return $ T.Node (RuleApp R.Ite [] e) [deriv1, deriv2]


proveMatchArm :: Id -> Prove TypedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf ctx
  arm@(MatchArm (PatTuple _ (Id _ x1) (Id _ x2)) e) q q' = do
  let (tx1, tx2) = splitTupleType $ getType arm
  if not $ isTree tx1 && isTree tx2 then do
    let ctx' = ctx `M.union` M.fromList [(x1, tx1), (x2, tx2)]
    deriv <- proveExpr tactic cf ctx' e q q'
    return ([], deriv)
  else errorFrom (SynArm arm) "match rule applied to a pair with more then one tree type."
proveMatchArm matchVar tactic cf ctx
  (MatchArm pat@(ConstPat _ id patVars) e) q q' = do
  pot <- view potential
  let tMatch = getType pat
  let (vars, tVars) = unzip $ mapMaybe getVar patVars
  let ctx' = M.delete matchVar ctx `M.union` M.fromList (zip vars tVars)
  p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (M.keys ctx')
  deriv <- proveExpr tactic cf ctx' e p q'
  let cs = cMatch pot q p matchVar vars
  tell cs
  return (cs, deriv)
  where getVar v@(Id _ id) = Just (id, getType v)
        getVar (WildcardVar _) = Nothing
proveMatchArm matchVar tactic cf ctx arm@(MatchArm pat@(Alias _ x) e) q q' = do
  if M.member x ctx then do
    deriv <- proveExpr tactic cf ctx e q q'
    return ([], deriv)
  else errorFrom (SynArm arm) "found invalid alias (variable not previosly defined) in match arm."
proveMatchArm _ _ _ _ arm _ _ = errorFrom (SynArm arm) "unsupported pattern match in rule (match)."

proveMatch :: Prove TypedExpr Derivation
proveMatch tactic cf ctx e@(Match (Var x) arms) q q' = do
  pot <- view potential
  let tactics = subTactics (length arms) tactic
  results <- zipWithM proveArmWithTactic tactics arms
  let (cs, derivs) = foldr accum ([], []) results
  tell cs
  return $ T.Node (RuleApp R.Match cs e) derivs
  where accum (cs, deriv) (css, derivs) = (cs ++ css, deriv:derivs)
        proveArmWithTactic tactic arm = proveMatchArm x tactic cf ctx arm q q'


splitLetCtx :: TypeCtx -> TypedExpr -> TypedExpr -> ProveMonad p (TypeCtx, TypeCtx)
splitLetCtx ctx e1 e2 = do
  let varsE1 = freeVars e1
  let varsE2 = freeVars e2
  let ctxE1 = M.restrictKeys ctx varsE1
  let ctxE2 = M.restrictKeys ctx varsE2
  
  if (ctx M.\\ (ctxE1 `M.union` ctxE2)) /= M.empty then
    errorFrom (SynExpr e1) $ "Found free variables in the body of a let binding which do not occur in Δ." ++ show ctxE1 ++ show ctxE2 ++ show ctx
  else return (ctxE1, ctxE2)

proveLet :: Prove TypedExpr Derivation
proveLet tactic cf ctx e@(Let x e1 e2) q q'
  | isTree $ getType e1 = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2
      let ctxE2' = M.insert x (getType e1) ctxE2 
      -- TODO if let binds a recursive call then use negative numbers for e
      let neg = False
      
      p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (M.keys ctxE1)
      p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure ["e"]
      r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (M.keys ctxE2')
      
      ps <- forAllCombinations' neg (M.keys ctxE2') x "P" (M.keys ctxE1)
      ps' <- forAllCombinations' neg (M.keys ctxE2') x "P'" ["e"]

      deriv1 <- proveExpr t1 cf ctxE1 e1 p p'
      deriv2 <- proveExpr t2 cf ctxE2' e2 r q'      
      cfDerivs <- zipWithM (proveExpr t1 True ctxE1 e1) (elems pot ps) (elems pot ps')

      let cs = cLet pot neg q p p' ps ps' r x
      tell cs
      return $ T.Node (RuleApp R.Let cs e) ([deriv1, deriv2] ++ cfDerivs)
  | otherwise = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2

      p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (M.keys ctxE1)
      p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure []
      deriv1 <- proveExpr t1 cf ctxE1 e1 p p'

      r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (M.keys ctxE2)
      deriv2 <- proveExpr t2 cf ctxE2 e2 r q'

      let cs = cLetBase pot q p r p'
      tell cs
      return $ T.Node (RuleApp R.Let cs e) [deriv1, deriv2]

proveApp :: Prove TypedExpr Derivation
proveApp tactic cf ctx e@(App id _) q q' = do
  pot <- view potential
  fnSig <- use sig
  let (p, p') = withCost $ fnSig M.! id
  let (r, r') = withoutCost $ fnSig M.! id
  let cs = cPlusMulti pot q p r
        ++ cPlusMulti pot q' p' r'
  tell cs
  return $ T.Node (RuleApp R.App cs e) []

proveWeakenVar :: Prove TypedExpr Derivation
proveWeakenVar tactic cf ctx e q q' = do
  pot <- view potential
  let redundantVars = M.keysSet ctx S.\\ freeVars e
  var <- if S.null redundantVars then
        errorFrom (SynExpr e) "Could not find a redundant variable to eleminate with the (w:var) rule."
        else
        return $ S.elemAt 0 redundantVars
  let ctx' = M.delete var ctx 
  let [t] = subTactics 1 tactic
  r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (M.keys ctx')
  deriv <- proveExpr t cf ctx' e r q'
  let cs = cWeakenVar pot q r
  tell cs
  return $ T.Node (RuleApp R.WeakenVar cs e) [deriv]
  
proveWeaken :: Prove TypedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken wArgs) _) cf ctx e q q' = do
  pot <- view potential
  let [t] = subTactics 1 tactic
  p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (args q)
  p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure (args q')
  let cs = cWeaken pot wArgs q q' p p'
  tell cs
  --deriv <- proveExpr t cf ctx e p p'
  deriv <- proveExpr t cf ctx e q q'
  return $ T.Node (RuleApp (R.Weaken wArgs) cs e) [deriv]

proveShift :: Prove TypedExpr Derivation
proveShift tactic cf ctx e q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic
  p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (args q)
  p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure (args q')
  let cs = cMinusVar pot p q
        ++ cMinusVar pot p' q'
  tell cs
  deriv <- proveExpr subTactic cf ctx e p p'
  return $ T.Node (RuleApp R.Shift cs e) [deriv]

proveTickDefer :: Prove TypedExpr Derivation
proveTickDefer tactic cf ctx e@(Tick c e1) q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic
  if cf then do
    deriv <- proveExpr subTactic cf ctx e1 q q'
    return $ T.Node (RuleApp R.TickDefer [] e) [deriv]
  else do
    p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (args q')
    let cs = cPlusConst pot p q' (fromMaybe 1 c) 
    tell cs
    deriv <- proveExpr subTactic cf ctx e1 q p
    return $ T.Node (RuleApp R.TickDefer cs e) [deriv]


proveExpr :: Prove TypedExpr Derivation
-- manual tactic
proveExpr (Rule R.Var []) cf ctx e@(Var _) = proveVar Auto cf ctx e
proveExpr (Rule R.Cmp []) cf ctx e@(Const {}) | isCmp e = proveCmp Auto cf ctx e
proveExpr (Rule R.Const []) cf ctx e@(Tuple {}) = provePair Auto cf ctx e
proveExpr (Rule R.Const []) cf ctx e@(Const {}) = proveConst Auto cf ctx e
proveExpr tactic@(Rule R.Match _) cf ctx e@(Match {}) = proveMatch tactic cf ctx e
proveExpr tactic@(Rule R.Ite _) cf ctx e@(Ite {}) = proveIte tactic cf ctx e
proveExpr tactic@(Rule R.Let _) cf ctx e@(Let {}) = proveLet tactic cf ctx e
proveExpr tactic@(Rule R.TickDefer _) cf ctx e = proveTickDefer tactic cf ctx e
proveExpr tactic@(Rule R.WeakenVar _) cf ctx e = proveWeakenVar tactic cf ctx e
proveExpr tactic@(Rule (R.Weaken _) _) cf ctx e = proveWeaken tactic cf ctx e
proveExpr tactic@(Rule R.Shift _) cf ctx e = proveShift tactic cf ctx e
proveExpr tactic@(Rule R.App _) cf ctx e@(App {}) = proveApp Auto cf ctx e
-- auto tactic
-- proveExpr Auto cf ctx e@Leaf = proveWeaken (Rule (R.Weaken []) [Auto]) cf ctx e
-- proveExpr Auto cf ctx e@(Var _) = proveVar Auto cf ctx e
-- proveExpr Auto cf ctx e@(Const _ _) | isCmp e = proveCmp Auto cf ctx e
-- proveExpr Auto cf ctx e@(Node {}) = proveNode Auto cf ctx e
-- proveExpr Auto cf ctx e@(Match _ _) = proveMatch Auto cf ctx e

proveExpr tactic _ _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"


ctxFromProdType :: Type -> [Id] -> TypeCtx
ctxFromProdType (TAp Prod ts) args = M.fromList $ filter (\(x, t) -> isTree t) $ zip args ts
ctxFromProdType t _ = error $ "Cannot construct a type context from the non product type '" ++ show t ++ "'."

proveFun :: Prove TypedFunDef Derivation
proveFun _ _ _ (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  let ctx = ctxFromProdType tFrom args
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic False ctx e q q'

proveModule :: HasCoeffs a => TypedModule -> ProveMonad a [Derivation]
proveModule mod = do
  s <- use sig
  -- TODO merge with existing signatures / or type check afterwards
  funAnns <- mapM (\f@(Fn name _ _) -> (name,) <$> genFunRsrcAnn f) mod
  sig .= s `M.union` M.fromList funAnns
  mapM proveFunWithAnn $ zip mod funAnns
  where proveFunWithAnn (fun, (_, ann)) = let (q, q') = withCost ann in
          proveFun Auto False M.empty fun q q' 
  
  
  

