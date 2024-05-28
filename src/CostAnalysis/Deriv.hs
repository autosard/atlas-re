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

--type Context = [Id]


--linRsrcAnn :: Int -> Int -> IndexedCoeffs
--linRsrcAnn id len = M.fromList [([x], Unknown id "Q" "lin" [x]) | x <- [1..(len+1)]]

--linPot :: GroundPot
--linPot = Potential linRsrcAnn 

--type CombPot = Potential [IndexedCoeffs]

--combRsrcAnn :: [GroundPot] -> Int -> Int -> [IndexedCoeffs]
--combRsrcAnn pots id len = map (\p -> rsrcAnn p id len) pots

--combPot :: [GroundPot] -> CombPot
--combPot pots = Potential (combRsrcAnn pots)
  
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

makeLenses ''ProofState

data ProofEnv a = ProofEnv {
  _potential :: Potential a,
  _tactics :: Map Id Tactic
  }

makeLenses ''ProofEnv


type ProveMonad p a = RWS (ProofEnv p) [Constraint] (ProofState p) a

genAnnIdPair :: ProveMonad a (Int, Int)
genAnnIdPair = do
  g <- use annIdGen
  let (next, nextNext) = (g, g+1)
  annIdGen .= nextNext + 1
  return (next, nextNext)

genFunRsrcAnn :: TypedFunDef -> ProveMonad a (a, a) 
genFunRsrcAnn fun = do
  pot <- view potential
  let (tFrom, tTo) = splitFnType . toType . tfType . funAnn $ fun
  let lenFrom = countTrees tFrom
  let lenTo = countTrees tTo
  (fromId, toId) <- genAnnIdPair
  let from = rsrcAnn pot fromId lenFrom
  let to = rsrcAnn pot toId lenTo
  return (from, to)

-- manualMode :: ProveMonad Bool
-- manualMode = isJust <$> use tactic

-- popRule :: Tactic -> ProveMonad Tactic
-- popRule = do
--   goals <- use subGoals
--   case goals of
--     [] -> 
  

type TypeCtx = Map Id Type

type Prove p e a = Maybe Tactic -> TypeCtx -> e -> p -> p -> ProveMonad p a

-- selectByTactic :: Tactic -> Prove a TypedFunDef Derivation

proveLeaf :: Prove a TypedExpr Derivation
proveLeaf _ ctx e q q' = do
  p <- view potential
  let cs = cLeaf p q q'
  tell cs
  return $ T.Node (Syn R.Leaf cs e) []
  

proveExpr :: Prove a TypedExpr Derivation
proveExpr (Just (Rule R.Leaf [])) ctx e = proveLeaf Nothing ctx e
proveExpr Nothing ctx e@Leaf = proveLeaf Nothing ctx e

ctxFromProdType :: Type -> [Id] -> TypeCtx
ctxFromProdType (TAp Prod ts) args = M.fromList $ filter (\(x, t) -> isTree t) $ zip args ts
ctxFromProdType t _ = error $ "Cannot construct a type context from the non product type '" ++ show t ++ "'."

proveFun :: Prove a TypedFunDef Derivation
proveFun _ _ (FunDef ann id args e) q q' = do
  let tFrom = fst . splitFnType . toType . tfType $ ann
  let ctx = ctxFromProdType tFrom args
  tactic <- M.lookup id <$> view tactics
  proveExpr tactic ctx e q q'
  

-- proveModule :: TypedModule -> ProveMonad a [Derivation]
-- proveModule mod = do
--   s <- use sig
--   -- TODO merge with existing signatures / or type check afterwards
--   funAnns <- mapM (\f@(Fn name _ _) -> (name,) <$> genFunRsrcAnn f) mod
--   sig .= s `M.union` M.fromList funAnns
--   mapM (\(fun, (_, (q, q'))) -> proveFun M.empty fun q q' ) $ zip mod funAnns
  
  
  

