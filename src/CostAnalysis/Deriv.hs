{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Deriv where

import Data.Tree(Tree)
import qualified Data.Tree as T
import Data.Map(Map)
import qualified Data.Map as M
import Z3.Monad
import Ast hiding (Coefficient)
import Primitive(Id)
import Control.Monad.RWS
import Lens.Micro.Platform
import Typing.Type
import Typing.Scheme (toType)
import CostAnalysis.Tactic
import qualified CostAnalysis.Rules as R
import CostAnalysis.Potential
import StaticAnalysis(freeVars)
import Data.Maybe (fromMaybe)

--type Context = [Id]

--linRsrcAnn :: Int -> Int -> IndexedCoeffs
--linRsrcAnn id len = M.fromList [([x], Unknown id "Q" "lin" [x]) | x <- [1..(len+1)]]

--linPot :: GroundPot
--linPot = Potential linRsrcAnn 
  
class Encodeable a where
  toZ3 :: a -> AST
  fromZ3 :: AST -> a

data RuleApp
  = Syn R.Rule [Constraint] TypedExpr
  | Struct R.Rule [Constraint] 

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


type ProveMonad p a = RWS (ProofEnv p) [Constraint] (ProofState p) a

genAnnIds :: Int -> ProveMonad a [Int]
genAnnIds n = do
  g <- use annIdGen
  annIdGen .= g+n
  return [g..(g+n-1)]

genAnnId :: ProveMonad a Int
genAnnId = do
  g <- use annIdGen
  annIdGen .= g+1
  return g

-- genAnnIdPair :: ProveMonad a (Int, Int)
-- genAnnIdPair = do
--   g <- use annIdGen
--   let (next, nextNext) = (g, g+1)
--   annIdGen .= nextNext + 1
--   return (next, nextNext)

-- genFunRsrcAnn :: TypedFunDef -> ProveMonad a (a, a) 
-- genFunRsrcAnn fun = do
--   pot <- view potential
--   let (tFrom, tTo) = splitFnType . toType . tfType . funAnn $ fun
--   let lenFrom = countTrees tFrom
--   let lenTo = countTrees tTo
--   (fromId, toId) <- genAnnIdPair
--   let from = rsrcAnn pot fromId lenFrom
--   let to = rsrcAnn pot toId lenTo
--   return (from, to)

-- manualMode :: ProveMonad Bool
-- manualMode = isJust <$> use tactic

-- popRule :: Tactic -> ProveMonad Tactic
-- popRule = do
--   goals <- use subGoals
--   case goals of
--     [] -> 
  

type TypeCtx = Map Id Type

type Prove p e a = Tactic -> Bool -> TypeCtx -> e -> p -> p -> ProveMonad p a

proveLeaf :: Prove a TypedExpr Derivation
proveLeaf _ _ ctx e q q' = do
  p <- view potential
  let cs = cLeaf p q q'
  tell cs
  return $ T.Node (Syn R.Leaf cs e) []

proveNode :: Prove a TypedExpr Derivation
proveNode _ _ ctx e q q' = do
  p <- view potential
  let cs = cNode p q q'
  tell cs
  return $ T.Node (Syn R.Node cs e) []

proveCmp :: Prove a TypedExpr Derivation
proveCmp _ _ _ e _ _ = do
  if not . isBool $ getType e then
    error "cmp rule applied to non-boolean expression."
  else return $ T.Node (Syn R.Cmp [] e) []

proveVar :: Prove a TypedExpr Derivation
proveVar _ _ _ e _ _ = return $ T.Node (Syn R.Var [] e) []

provePair :: Prove a TypedExpr Derivation
provePair _ _ ctx e@(Tuple (Var x1) (Var x2)) _ _ = do
  if not $ isTree (ctx M.!x1) && isTree (ctx M.!x2) then
    return $ T.Node (Syn R.Var [] e) []
  else error "pair rule applied to more then one tree type."

proveIte :: Prove a TypedExpr Derivation
proveIte tactic cf ctx e@(Ite _ e1 e2) q q' = do
  let [t1, t2] = subTactics 2 tactic
  deriv1 <- proveExpr t1 cf ctx e1 q q'
  deriv2 <- proveExpr t2 cf ctx e1 q q'
  return $ T.Node (Syn R.Ite [] e) [deriv1, deriv2]

proveMatch :: Prove a TypedExpr Derivation
proveMatch tactic cf ctx
  e@(Match (Var x)
     [MatchArm (PatTreeLeaf _) e1,
      armNode@(MatchArm (PatTreeNode _ (Id idR) (Id idV) (Id idL)) e2)])
  q q' = do
  pot <- view potential
  let [t1, t2] = subTactics 2 tactic
  
  p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (annLen pot q - 1) 
  let ctxLeaf = M.delete x ctx
  derivLeaf <- proveExpr t1 cf ctxLeaf e1 p q'

  r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (annLen pot q + 1)
  let (tl, tv, tr) = splitTreeType $ getType armNode
  let ctxNode = ctx `M.union` M.fromList [(idL, tl), (idV, tv), (idR, tr)]
  derivNode <- proveExpr t2 cf ctxNode e2 r q'
  
  let cs = cMatch pot q p r
  tell cs
  return $ T.Node (Syn R.Match cs e) [derivLeaf, derivNode]
proveMatch tactic cf ctx
  e@(Match (Var x)
    [arm@(MatchArm (PatTuple _ (Id x1) (Id x2)) eInner)])
  q q' = do
  let (tx1, tx2) = splitTupleType $ getType arm
  if not $ isTree tx1 && isTree tx2 then do
    let [subTactic] = subTactics 1 tactic
    let ctx' = ctx `M.union` M.fromList [(x1, tx1), (x2, tx2)]
    deriv <- proveExpr subTactic cf ctx' eInner q q'
    return $ T.Node (Syn R.Match [] e) [deriv]
  else error "match-pair rule applied to a pair with more then one tree type."

splitLetCtx :: TypeCtx -> TypedExpr -> TypedExpr -> (TypeCtx, TypeCtx)
splitLetCtx ctx e1 e2 = do
  let varsE1 = freeVars e1
  let varsE2 = freeVars e2
  let ctxE1 = M.restrictKeys ctx varsE1
  let ctxE2 = M.restrictKeys ctx varsE2
  
  if (ctx M.\\ (ctxE1 `M.union` ctxE2)) /= M.empty then
    error "Found free variables in the body of a let binding which do not occur in Δ."
  else (ctxE1, ctxE2)

proveLet :: Prove a TypedExpr Derivation
proveLet tactic cf ctx e@(Let x e1 e2) q q'
  | isTree $ getType e1 = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      let (ctxE1, ctxE2) = splitLetCtx ctx e1 e2

      -- TODO if let binds a recursive call then use negive numbers for e
      let neg = True
      
      p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (length ctxE1)
      p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure 0
      r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (length ctxE2)
      let pIdxs = enumAnn pot r neg
      pIds <- genAnnIds (length pIdxs)
      let ps = forAllIdx pot pIdxs pIds p
      let p'Idxs = enumAnn pot r neg
      p'Ids <- genAnnIds (length p'Idxs)
      let ps' = forAllIdx pot p'Idxs p'Ids p'

      deriv1 <- proveExpr t1 cf ctxE1 e1 p p'
      deriv2 <- proveExpr t2 cf ctxE2 e2 r q'      
      cfDerivs <- zipWithM (proveExpr t1 True ctxE1 e1) (elems pot ps) (elems pot ps')

      let cs = cLet pot neg q p p' ps ps' r
      tell cs
      return $ T.Node (Syn R.Let cs e) (deriv1:deriv2:cfDerivs)
  | otherwise = do
      pot <- view potential
      let [t1, t2] = subTactics 2 tactic
      let (ctxE1, ctxE2) = splitLetCtx ctx e1 e2

      p <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (length ctxE1)
      p' <- rsrcAnn pot <$> genAnnId <*> pure "P'" <*> pure 0
      deriv1 <- proveExpr t1 cf ctxE1 e1 p p'

      r <- rsrcAnn pot <$> genAnnId <*> pure "R" <*> pure (length ctxE2)
      deriv2 <- proveExpr t2 cf ctxE2 e2 r q'

      let cs = cLetBase pot q p r p'
      tell cs
      return $ T.Node (Syn R.Let cs e) [deriv1, deriv2]
      

proveTickDefer :: Prove a TypedExpr Derivation
proveTickDefer tactic cf ctx e@(Tick c e1) q q' = do
  pot <- view potential
  let [subTactic] = subTactics 1 tactic
  if cf then do
    deriv <- proveExpr subTactic cf ctx e1 q q'
    return $ T.Node (Syn R.TickDefer [] e) [deriv]
    else do
    q'' <- rsrcAnn pot <$> genAnnId <*> pure "P" <*> pure (annLen pot q')
    let cs = cMinusConst pot q' (fromMaybe 1 c) q''
    tell cs
    deriv <- proveExpr subTactic cf ctx e1 q q''
    return $ T.Node (Syn R.TickDefer cs e) [deriv]

proveExpr :: Prove a TypedExpr Derivation
proveExpr (Rule R.Leaf []) cf ctx e = proveLeaf Auto cf ctx e
proveExpr Auto cf ctx e@Leaf = proveLeaf Auto cf ctx e

ctxFromProdType :: Type -> [Id] -> TypeCtx
ctxFromProdType (TAp Prod ts) args = M.fromList $ filter (\(x, t) -> isTree t) $ zip args ts
ctxFromProdType t _ = error $ "Cannot construct a type context from the non product type '" ++ show t ++ "'."

-- proveFun :: Prove a TypedFunDef Derivation
-- proveFun _ _ (FunDef ann id args e) q q' = do
--   let tFrom = fst . splitFnType . toType . tfType $ ann
--   let ctx = ctxFromProdType tFrom args
--   tactic <- fromMaybe Auto . M.lookup id <$> view tactics
--   proveExpr tactic ctx e q q'
  

-- proveModule :: TypedModule -> ProveMonad a [Derivation]
-- proveModule mod = do
--   s <- use sig
--   -- TODO merge with existing signatures / or type check afterwards
--   funAnns <- mapM (\f@(Fn name _ _) -> (name,) <$> genFunRsrcAnn f) mod
--   sig .= s `M.union` M.fromList funAnns
--   mapM (\(fun, (_, (q, q'))) -> proveFun M.empty fun q q' ) $ zip mod funAnns
  
  
  

