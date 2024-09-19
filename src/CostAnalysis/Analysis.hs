{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

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
import Ast hiding (CostAnnotation)
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
  mapM_ (createAnn rhs . (defs mod M.!)) fns
  derivs <- mapM (analyzeFn . (defs mod M.!)) fns
  fnDerivs %= (++derivs)
  solution <- solve fns
  addSigCs fns solution
  tell solution

createAnn :: RsrcAnn -> PositionedFunDef -> ProveMonad ()
createAnn rhs def@(Fn fn _ _) = do
  let rhs' = case tfCostAnn $ funAnn def of
        Just (Cost True _) -> Nothing
        _notWorstCase -> Just rhs
  ann <- genFunRsrcAnn rhs' def
  sig %= M.insert fn ann

analyzeFn :: PositionedFunDef -> ProveMonad Derivation
analyzeFn def@(FunDef funAnn fnId _ body) = do
  mode <- view analysisMode
  
  case mode of
    CheckCoefficients -> case tfCostAnn funAnn of
      Just Coeffs {..} -> coeffsMatchAnnotation fnId (caWithCost, caWithoutCost)
      Just (Cost True cost) -> coeffsMatchAnnotation fnId ((cost, M.empty) , Nothing)
      _noCoeff -> errorFrom (SynExpr body) "Missing resource coefficient annotation for check-coeffs mode."
    CheckCost -> case tfCostAnn funAnn of
      Just Cost {..} -> cmpCostWithAnn annLikeConstEq fnId costCoeffs
      _noCost -> errorFrom (SynExpr body) "Missing cost annotation for check-cost mode."
    ImproveCost -> case tfCostAnn funAnn of
      Just Cost {..} -> do
        cmpCostWithAnn annLikeConstLe fnId costCoeffs
        addSimpleCostOptimization fnId
      noCost_ -> errorFrom (SynExpr body) "Missing cost annotation for improve-cost mode."
    Infer -> addFullCostOptimization fnId
  proveFun def


type CostComparision = PointWiseOp -> Map CoeffIdx Rational -> [Constraint]

cmpCostWithAnn :: CostComparision -> Id -> Map CoeffIdx Rational -> ProveMonad ()
cmpCostWithAnn cmp fn costAnn = do
  ann <- (M.! fn) <$> use sig
  let cost = symbolicCost (withCost ann)
  tellSigCs $ cmp cost costAnn

coeffsMatchAnnotation :: Id -> (Ast.FunRsrcAnn, Maybe Ast.FunRsrcAnn) -> ProveMonad ()
coeffsMatchAnnotation fn (annWithCost, annWithoutCost) = do
  ann <- (M.! fn) <$> use sig
  let (p, p') = withoutCost ann
  let (q, q') = withCost ann  
  tellSigCs (annLikeConstEq q $ fst annWithCost)
  tellSigCs (annLikeConstEq q' $ snd annWithCost)
  tellSigCs . concat . maybeToList $ (annLikeConstEq p . fst <$> annWithoutCost)
  tellSigCs . concat . maybeToList $ (annLikeConstEq p' . snd <$> annWithoutCost)

addSimpleCostOptimization :: Id -> ProveMonad ()
addSimpleCostOptimization fn = do
  ann <- (M.! fn) <$> use sig
  let cost = symbolicCost (withCost ann)
  let costTerm = sum $ M.elems (opCoeffs cost)
  optiTargets %= (costTerm:)

  
addFullCostOptimization :: Id -> ProveMonad ()
addFullCostOptimization fn = do
  pot <- view potential
  ann <- (M.! fn) <$> use sig
  let (q, q') = withCost ann
  let costTerm = cOptimize pot q q'
  optiTargets %= (costTerm:)
  

genFunRsrcAnn :: Maybe RsrcAnn -> PositionedFunDef -> ProveMonad CostAnalysis.RsrcAnn.FunRsrcAnn
genFunRsrcAnn rhs fun = do
  let (argsFrom, argsTo) = ctxFromFn fun
  to <- case rhs of
    Just ann -> return ann
    Nothing -> emptyAnn "Q'" "fn" argsTo
  from <- defaultAnn "Q" "fn" argsFrom
  fromCf <- defaultAnn "P" "fn cf" argsFrom
  toCf <- defaultAnn "P'" "fn cf" argsTo
  return $ FunRsrcAnn (from, to) (fromCf, toCf)

  
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
