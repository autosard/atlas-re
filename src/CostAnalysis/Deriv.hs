{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Deriv where

import Data.Tree(Tree)
import qualified Data.Tree as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Text(Text)
import Z3.Monad ( AST, getBoolValue )
import Ast hiding (Coefficient)
import Primitive(Id)
import Control.Monad.RWS
import Control.Monad.Except
import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe)
import SourceError

import qualified Debug.Trace(trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

--type Context = [Id]

--linRsrcAnn :: Int -> Int -> IndexedCoeffs
--linRsrcAnn id len = M.fromList [([x], Unknown id "Q" "lin" [x]) | x <- [1..(len+1)]]

--linPot :: GroundPot
--linPot = Potential linRsrcAnn 
  
class Encodeable a where
  toZ3 :: a -> AST
  fromZ3 :: AST -> a

data RuleApp = RuleApp R.Rule [Constraint] TypedExpr

type Derivation = Tree RuleApp

data ProofState a = ProofState {
  _sig :: Map Id (a, a),
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

type ProofResult = ([Derivation], [Constraint])

runProof :: TypedModule -> Potential a -> Map Id Tactic
  -> Either SourceError ProofResult
runProof mod pot tactics = (,cs) <$> deriv
  where (deriv, cs) = evalRWS rws env state  
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

genFunRsrcAnn :: TypedFunDef -> ProveMonad a (a, a) 
genFunRsrcAnn fun = do
  pot <- view potential
  let (tFrom, tTo) = splitFnType . toType . tfType . funAnn $ fun
  let lenFrom = countTrees tFrom
  let lenTo = countTrees tTo
  (fromId, toId) <- genAnnIdPair
  let from = rsrcAnn pot fromId "Q" lenFrom
  let to = rsrcAnn pot toId "Q'" lenTo
  return (from, to)
 

type TypeCtx = Map Id Type

type Prove p e a = Tactic -> Bool -> TypeCtx -> e -> p -> p -> ProveMonad p a

errorFrom :: Syntax Typed -> String -> ProveMonad p a
errorFrom e msg = throwError $ SourceError loc msg
  where loc = case (teSrc . getAnn) e of
          (Loc pos) -> pos
          (DerivedFrom pos) -> pos

proveLeaf :: Prove a TypedExpr Derivation
proveLeaf _ _ ctx e q q' = do
  p <- view potential
  let cs = cLeaf p q q'
  tell cs
  return $ T.Node (RuleApp R.Leaf cs e) []

proveNode :: Prove a TypedExpr Derivation
proveNode _ _ ctx e q q' = do
  p <- view potential
  let cs = cNode p q q'
  tell cs
  return $ T.Node (RuleApp R.Node cs e) []

proveCmp :: Prove a TypedExpr Derivation
proveCmp _ _ _ e _ _ = do
  if not . isBool $ getType e then
    errorFrom (SynExpr e) "cmp rule applied to non-boolean expression."
  else return $ T.Node (RuleApp R.Cmp [] e) []

proveVar :: Prove a TypedExpr Derivation
proveVar _ _ _ e _ _ = return $ T.Node (RuleApp R.Var [] e) []

provePair :: Prove a TypedExpr Derivation
provePair _ _ ctx e@(Tuple (Var x1) (Var x2)) _ _ = do
  if not $ isTree (ctx M.!x1) && isTree (ctx M.!x2) then
    return $ T.Node (RuleApp R.Var [] e) []
  else errorFrom (SynExpr e) "pair rule applied to more then one tree type."

proveIte :: Prove a TypedExpr Derivation
proveIte tactic cf ctx e@(Ite _ e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  deriv1 <- proveExpr t1 cf ctx e1 q q'
  deriv2 <- proveExpr t2 cf ctx e2 q q'
  return $ T.Node (RuleApp R.Ite [] e) [deriv1, deriv2]


proveMatchArm :: Id -> Prove a TypedMatchArm ([Constraint], Derivation)
proveMatchArm matchVar tactic cf ctx (MatchArm (PatTreeLeaf _) e) q q' = do
  pot <- view potential
  let ctx' = M.delete matchVar ctx
  -- just p-leaf this is gonna work
  p <- rsrcAnn pot <$> genAnnId <*> pure "P(leaf)" <*> pure (annLen pot q - 1) 
  deriv <- proveExpr tactic cf ctx' e p q'
  let cs = cMatchLeaf pot q p
  tell cs
  return (cs, deriv)
proveMatchArm matchVar tactic cf ctx
  (MatchArm pat@(PatTreeNode _ (Id idR) (Id idV) (Id idL)) e) q q' = do
  pot <- view potential
  let tTree = getType pat
  let tValue = treeValueType tTree
  let ctx' = M.delete matchVar ctx `M.union` M.fromList [(idL, tTree), (idR, tTree)]
  r <- rsrcAnn pot <$> genAnnId <*> pure "R(node)" <*> pure (annLen pot q + 1)
  deriv <- proveExpr tactic cf ctx' e r q'
  let cs = cMatchNode pot q r
  tell cs
  return (cs, deriv)
proveMatchArm matchVar tactic cf ctx
  arm@(MatchArm (PatTuple _ (Id x1) (Id x2)) e) q q' = do
  let (tx1, tx2) = splitTupleType $ getType arm
  if not $ isTree tx1 && isTree tx2 then do
    let ctx' = ctx `M.union` M.fromList [(x1, tx1), (x2, tx2)]
    deriv <- proveExpr tactic cf ctx' e q q'
    return ([], deriv)
  else errorFrom (SynArm arm) "match-pair rule applied to a pair with more then one tree type."
proveMatchArm matchVar tactic cf ctx arm@(MatchArm pat@(Alias _ x) e) q q' = do
  if M.member x ctx then do
    deriv <- proveExpr tactic cf ctx e q q'
    return ([], deriv)
  else errorFrom (SynArm arm) "found invalid alias (variable not previosly defined) in match arm."
proveMatchArm _ _ _ _ arm _ _ = errorFrom (SynArm arm) "unsupported pattern match in rule (match)."

proveMatch :: Prove a TypedExpr Derivation
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

proveLet :: Prove a TypedExpr Derivation
proveLet tactic cf ctx e@(Let x e1 e2) q q'
  | isTree $ getType e1 = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2

      -- TODO if let binds a recursive call then use negive numbers for e
      let neg = True
      
      p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (length ctxE1)
      p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure 0
      r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (length ctxE2)
      let pIdxs = enumAnn pot (annLen pot r) neg
      pIds <- genAnnIds (length pIdxs)
      let ps = forAllIdx pot pIdxs pIds (annLen pot p)
      let p'Idxs = enumAnn pot (annLen pot r) neg
      p'Ids <- genAnnIds (length p'Idxs)
      let ps' = forAllIdx pot p'Idxs p'Ids (annLen pot p')

      deriv1 <- proveExpr t1 cf ctxE1 e1 p p'
      deriv2 <- proveExpr t2 cf ctxE2 e2 r q'      
      --cfDerivs <- zipWithM (proveExpr t1 True ctxE1 e1) (elems pot ps) (elems pot ps')

      let cs = cLet pot neg q p p' ps ps' r
      tell cs
      return $ T.Node (RuleApp R.Let cs e) (deriv1:[deriv2])-- :cfDerivs)
  | otherwise = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      (ctxE1, ctxE2) <- splitLetCtx ctx e1 e2

      p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (length ctxE1)
      p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure 0
      deriv1 <- proveExpr t1 cf ctxE1 e1 p p'

      r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (length ctxE2)
      deriv2 <- proveExpr t2 cf ctxE2 e2 r q'

      let cs = cLetBase pot q p r p'
      tell cs
      return $ T.Node (RuleApp R.Let cs e) [deriv1, deriv2]

proveWeaken :: Prove a TypedExpr Derivation
proveWeaken tactic@(Rule (R.Weaken args) _) cf ctx e q q' = do
  pot <- view potential
  let [t] = subTactics 1 tactic
  p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (annLen pot q)
  p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure (annLen pot q')
  let cs = cWeaken pot args q q' p p'
  tell cs
  deriv <- proveExpr t cf ctx e p p'
  return $ T.Node (RuleApp (R.Weaken args) cs e) [deriv]

proveShift :: Prove a TypedExpr Derivation
proveShift tactic cf ctx e q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic
  p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (annLen pot q)
  p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure (annLen pot q')
  let cs = cMinusVar pot q  p
        ++ cMinusVar pot q' p'
  deriv <- proveExpr subTactic cf ctx e p p'
  return $ T.Node (RuleApp R.Shift cs e) [deriv]
  

proveTickDefer :: Prove a TypedExpr Derivation
proveTickDefer tactic cf ctx e@(Tick c e1) q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic
  if cf then do
    deriv <- proveExpr subTactic cf ctx e1 q q'
    return $ T.Node (RuleApp R.TickDefer [] e) [deriv]
  else do
    p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (annLen pot q')
    let cs = cPlusConst pot q' (fromMaybe 1 c) p
    tell cs
    deriv <- proveExpr subTactic cf ctx e1 q p
    return $ T.Node (RuleApp R.TickDefer cs e) [deriv]


proveExpr :: Prove a TypedExpr Derivation
-- manual tactic
proveExpr (Rule R.Var []) cf ctx e = proveVar Auto cf ctx e
proveExpr (Rule R.Leaf []) cf ctx e = proveLeaf Auto cf ctx e
proveExpr (Rule R.Node []) cf ctx e = proveNode  Auto cf ctx e
proveExpr (Rule R.Cmp []) cf ctx e@(Const _ _) | isCmp e = proveCmp Auto cf ctx e
proveExpr tactic@(Rule R.Match _) cf ctx e = proveMatch tactic cf ctx e
proveExpr tactic@(Rule R.Ite _) cf ctx e@(Ite {}) = proveIte tactic cf ctx e
proveExpr tactic@(Rule R.Let _) cf ctx e = proveLet tactic cf ctx e
proveExpr tactic@(Rule R.TickDefer _) cf ctx e = proveTickDefer tactic cf ctx e
proveExpr tactic@(Rule (R.Weaken _) _) cf ctx e = proveWeaken tactic cf ctx e
proveExpr tactic@(Rule R.Shift _) cf ctx e = proveShift tactic cf ctx e
-- auto tactic
proveExpr Auto cf ctx e@Leaf = proveWeaken (Rule (R.Weaken []) [Auto]) cf ctx e
proveExpr Auto cf ctx e@(Var _) = proveVar Auto cf ctx e
proveExpr Auto cf ctx e@(Const _ _) | isCmp e = proveCmp Auto cf ctx e
proveExpr Auto cf ctx e@(Node {}) = proveNode Auto cf ctx e
proveExpr Auto cf ctx e@(Match _ _) = proveMatch Auto cf ctx e

proveExpr tactic _ _ e = \_ _ -> errorFrom (SynExpr e) $ "Could not apply tactic to given "
  ++ printExprHead e ++ " expression. Tactic: '" ++ printTacticHead tactic ++ "'"


ctxFromProdType :: Type -> [Id] -> TypeCtx
ctxFromProdType (TAp Prod ts) args = M.fromList $ filter (\(x, t) -> isTree t) $ zip args ts
ctxFromProdType t _ = error $ "Cannot construct a type context from the non product type '" ++ show t ++ "'."

proveFun :: Prove a TypedFunDef Derivation
proveFun _ _ _ (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  let ctx = ctxFromProdType tFrom args
  tactic <- fromMaybe Auto . M.lookup id <$> view tactics
  proveExpr tactic False ctx e q q'

proveModule :: TypedModule -> ProveMonad a [Derivation]
proveModule mod = do
  s <- use sig
  -- TODO merge with existing signatures / or type check afterwards
  funAnns <- mapM (\f@(Fn name _ _) -> (name,) <$> genFunRsrcAnn f) mod
  sig .= s `M.union` M.fromList funAnns
  mapM (\(fun, (_, (q, q'))) -> proveFun Auto False M.empty fun q q' ) $ zip mod funAnns
  
  
  

