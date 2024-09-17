{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Analysis where

import Prelude hiding (sum)
import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T
import Data.Maybe(maybeToList)
import Lens.Micro.Platform

import Primitive(Id)
import Ast
import CostAnalysis.Solving (solve)
import CostAnalysis.ProveMonad
import CostAnalysis.Constraint
import SourceError
import CostAnalysis.Rules
import Control.Monad.Except (MonadError(throwError))
import CostAnalysis.Deriv
import CostAnalysis.Coeff
import Typing.Type
import CostAnalysis.RsrcAnn (RsrcAnn, RsrcSignature,
                             FunRsrcAnn(..), annLikeConstEq,
                             annLikeConstLe, PointWiseOp,
                             opCoeffs)
import CostAnalysis.Potential(symbolicCost, cOptimize)


analyzeModule :: ProofEnv -> PositionedModule
  -> IO (Either SourceError (Derivation, RsrcSignature, Either [Constraint] Solution))
analyzeModule env mod = do
  let state = ProofState M.empty [] [] 0 0 [] [] M.empty
  case argsForRHS mod of
    Left err -> return $ Left err
    Right arg -> do
      (result, state', solution) <- runProof env state (analyzeModule' mod)
      let deriv = T.Node (ProgRuleApp mod) (state'^.fnDerivs)
      case result of
        Left (DerivErr srcErr) -> return (Left srcErr)
        Left (UnsatErr core) -> return (Right (deriv, state'^.sig, Left core))
        Right _ -> return (Right (deriv, state'^.sig, Right solution))

analyzeModule' :: PositionedModule -> ProveMonad ()
analyzeModule' mod = 
  case argsForRHS mod of
    Left err -> throwError $ DerivErr err
    Right args -> do
      -- unique right hand side for the whole module
      rhs <- defaultAnn "Q'" "fn" args
      incr <- view incremental
      if incr then
        mapM_ (analyzeBindingGroup mod rhs) (mutRecGroups mod)
      else
        analyzeBindingGroup mod rhs (concat $ mutRecGroups mod)
  
analyzeBindingGroup :: PositionedModule -> RsrcAnn -> [Id]  -> ProveMonad ()
analyzeBindingGroup mod rhs fns = do
  mapM_ (createAnn rhs) fns
  derivs <- mapM analyzeFn fns
  fnDerivs %= (++derivs)
  solution <- solve fns
  addSigCs fns solution
  tell solution
  where createAnn rhs fn = do
          ann <- genFunRsrcAnn rhs $ defs mod M.! fn
          sig %= M.insert fn ann
        analyzeFn fn = do
          let def = defs mod M.! fn
          mode <- view analysisMode
          case mode of
            CheckCoefficients -> coeffsMatchAnnotation def
            CheckCost -> cmpCostWithAnn annLikeConstEq def
            ImproveCost -> do
              cmpCostWithAnn annLikeConstLe def
              addSimpleCostOptimization def
            Infer -> addFullCostOptimization def
          proveFun def

type CostComparision = PointWiseOp -> Map CoeffIdx Rational -> [Constraint]

cmpCostWithAnn :: CostComparision -> PositionedFunDef -> ProveMonad ()
cmpCostWithAnn cmp fun@(FunDef funAnn fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  let cost = symbolicCost (withCost ann)
  tellSigCs . concat . maybeToList $ (cmp cost <$> tfCost funAnn)

coeffsMatchAnnotation :: PositionedFunDef -> ProveMonad ()
coeffsMatchAnnotation fun@(FunDef funAnn fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  let (p, p') = withoutCost ann
  let (q, q') = withCost ann  
  tellSigCs . concat . maybeToList $ (annLikeConstEq q . fst <$> tfRsrcWithCost funAnn)
  tellSigCs . concat . maybeToList $ (annLikeConstEq q' . snd <$> tfRsrcWithCost funAnn)
  tellSigCs . concat . maybeToList $ (annLikeConstEq p . fst <$> tfRsrcWithoutCost funAnn)
  tellSigCs . concat . maybeToList $ (annLikeConstEq p' . snd <$> tfRsrcWithoutCost funAnn)

addSimpleCostOptimization :: PositionedFunDef -> ProveMonad ()
addSimpleCostOptimization fun@(FunDef funAnn fnId _ _) = do
  ann <- (M.! fnId) <$> use sig
  let cost = symbolicCost (withCost ann)
  let costTerm = sum $ M.elems (opCoeffs cost)
  optiTargets %= (costTerm:)

  
addFullCostOptimization :: PositionedFunDef -> ProveMonad ()
addFullCostOptimization fun@(FunDef funAnn fnId _ _) = do
  pot <- view potential
  ann <- (M.! fnId) <$> use sig
  let (q, q') = withCost ann
  let costTerm = cOptimize pot q q'
  optiTargets %= (costTerm:)
  

genFunRsrcAnn :: RsrcAnn -> PositionedFunDef -> ProveMonad FunRsrcAnn
genFunRsrcAnn rhs fun = do
  let (argsFrom, argsTo) = ctxFromFn fun
  from <- defaultAnn "Q" "fn" argsFrom
  fromCf <- defaultAnn "P" "fn cf" argsFrom
  toCf <- defaultAnn "P'" "fn cf" argsTo
  return $ FunRsrcAnn (from, rhs) (fromCf, toCf)

  
addSigCs :: [Id] -> Solution -> ProveMonad ()
addSigCs fns solution = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  let cs = concatMap go (getCoeffs sig')
  sigCs %= (++cs)
  where go coeff = eq (CoeffTerm coeff) (ConstTerm (solution M.! coeff))


-- TODO this breaks RandSplayTree.delete because splay max returns a tuple not a single tree.  
argsForRHS :: Module Positioned -> Either SourceError [(Id, Type)]
argsForRHS mod = Right $ head args
  -- if allSame args then Right $ head args else
  -- Left $ SourceError (tfLoc $ funAnn (head $ fns mod))
  -- "Cost analysis requries all involved functions to have the same return type to guarantee a consistent potential function."
  where args = map go (concat $ mutRecGroups mod)
        go fn = snd . ctxFromFn $ defs mod M.! fn
