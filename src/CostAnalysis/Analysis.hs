{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Analysis where

import Prelude hiding (sum, (!?))
import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T
import Data.Maybe(mapMaybe, fromMaybe)
import Lens.Micro.Platform

import Primitive(Id)
import Ast hiding (CostAnnotation)
import CostAnalysis.Solving (solve)
import CostAnalysis.ProveMonad
import CostAnalysis.Constraint hiding (and)
import SourceError
import CostAnalysis.Rules
import Control.Monad.Except (MonadError (throwError))
import CostAnalysis.Deriv
import CostAnalysis.Coeff
import Typing.Type
import CostAnalysis.RsrcAnn ( RsrcSignature,
                             FunRsrcAnn(..), ctxConstEq,
                             ctxConstLe, PointWiseOp,
                             opCoeffs, ctxGeZero, AnnCtx, annLikeLeftInRight, (!?), ctxZipWith, pointWiseZero, RsrcAnn (RsrcAnn))
import CostAnalysis.Potential(ctxSymbolicCost, PotFnMap, Potential (cExternal))
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential.Kind (fromKind)
import Control.Monad.Extra (concatMapM)


defaultPotentialMap = M.fromList
  [
    (ListType, Polynomial),
    (TreeType, Logarithmic)
  ]


initPotentials :: PositionedModule -> Map Type PotentialKind -> ProveMonad PotFnMap
initPotentials mod kinds = do 
  potFnArgs <- argsForRHS (M.elems $ defs mod) (M.keys kinds)
  M.fromList <$> mapM go (M.toAscList potFnArgs)
  where go (t, args) = do
          let pot = fromKind (kinds M.! t)
          potFn <- defaultAnn' pot "Q'" "potFn" args
          return (t, (pot, potFn))
                         

analyzeModule :: ProofEnv -> PositionedModule
  -> IO (Either SourceError (Derivation, RsrcSignature, Either [Constraint] (Solution, PotFnMap)))
analyzeModule env mod = do
  
  let state = ProofState M.empty [] [] 0 0 [] [] M.empty M.empty 
  (result, state', solution) <- runProof env state (analyzeModule' mod)
  let deriv = T.Node (ProgRuleApp mod) (state'^.fnDerivs)
  case result of
    Left (DerivErr srcErr) -> return (Left srcErr)
    Left (UnsatErr core) -> return (Right (deriv, state'^.sig, Left core))
    Right _ -> return (Right (deriv, state'^.sig, Right (solution, state'^.potentials)))



analyzeModule' :: PositionedModule -> ProveMonad ()
analyzeModule' mod = do
  pots <- initPotentials mod $ modPotentialMap mod `M.union` defaultPotentialMap
  potentials %= const pots
  incr <- view incremental
  if incr then
    mapM_ (analyzeBindingGroup mod) (mutRecGroups mod)
  else
    analyzeBindingGroup mod (concat $ mutRecGroups mod)

analyzeBindingGroup :: PositionedModule -> [Id]  -> ProveMonad ()
analyzeBindingGroup mod fns = do
  derivs <- mapM (analyzeFn mod . (defs mod M.!)) fns
  fnDerivs %= (++derivs)
  solution <- solve fns
  addSigCs fns solution
  tell solution

analyzeFn :: PositionedModule -> PositionedFunDef -> ProveMonad Derivation
analyzeFn mod fn@(Fn id _ _) = do
  ann <- genFunRsrcAnn fn
  sig %= M.insert id ann
  analyzeFn' fn

analyzeFn' :: PositionedFunDef -> ProveMonad Derivation
analyzeFn' def@(FunDef funAnn fnId _ body) = do
  mode <- view analysisMode
  
  case mode of
    CheckCoefficients -> case tfCostAnn funAnn of
      Just Coeffs {..} -> coeffsMatchAnnotation fnId (caWithCost, caWithoutCost)
      Just (Cost True cost) -> coeffsMatchAnnotation fnId ((cost, M.empty) , [])
      _noCoeff -> errorFrom (SynExpr body) "Missing resource coefficient annotation for check-coeffs mode."
    CheckCost -> case tfCostAnn funAnn of
      Just Cost {..} -> cmpCostWithAnn ctxConstEq fnId costCoeffs
      _noCost -> errorFrom (SynExpr body) "Missing cost annotation for check-cost mode."
    ImproveCost -> case tfCostAnn funAnn of
      Just Cost {..} -> do
        cmpCostWithAnn ctxConstLe fnId costCoeffs
        addSimpleCostOptimization fnId
      noCost_ -> errorFrom (SynExpr body) "Missing cost annotation for improve-cost mode."
    Infer -> do
      s <- use sig
      let (q, q') = withCost $ s M.! fnId
      tellCs $ potFnCovered q q'
      tellCs =<< externalCsForCtx q q'
      addFullCostOptimization fnId
  proveFun def

externalCsForCtx :: AnnCtx -> AnnCtx -> ProveMonad [Constraint]
externalCsForCtx ctxQ ctxQ' = concatMapM csForType (M.assocs ctxQ) 
  where csForType :: (Type, RsrcAnn) -> ProveMonad [Constraint]
        csForType (t, q) = do
          pots <- use potentials
          if M.member t ctxQ' then
            return $ cExternal (potForType t pots ) q (ctxQ' M.! t)
          else
            return []

potFnCovered :: AnnCtx -> AnnCtx -> [Constraint]
potFnCovered qs qs' = concat
  [annLikeLeftInRight q' q
  | t <- M.keys qs',
    let q' = qs' M.! t,
    M.member t qs,
    let q = qs M.! t]

type CostComparision = Map Type PointWiseOp -> Map Type CoeffAnnotation -> [Constraint]

cmpCostWithAnn :: CostComparision -> Id -> Map Type CoeffAnnotation -> ProveMonad ()
cmpCostWithAnn cmp fn costAnn = do
  ann <- (M.! fn) <$> use sig
  let cost = ctxSymbolicCost (withCost ann)
  tellSigCs $ ctxGeZero cost
  tellSigCs $ cmp cost costAnn

coeffsMatchAnnotation :: Id -> (Ast.FunRsrcAnn, [Ast.FunRsrcAnn]) -> ProveMonad ()
coeffsMatchAnnotation fn (annWithCost, annsWithoutCost) = do
  ann <- (M.! fn) <$> use sig
  let cfAnns = withoutCost ann
  let (q, q') = withCost ann
  tellSigCs $ ctxConstEq q $ fst annWithCost
  tellSigCs $ ctxConstEq q' $ snd annWithCost
  zipWithM_ matchCf cfAnns annsWithoutCost
  where matchCf (pIs, pIs') (pShould, pShould') = do
          tellSigCs $ ctxConstEq pIs pShould
          tellSigCs $ ctxConstEq pIs' pShould'

addSimpleCostOptimization :: Id -> ProveMonad ()
addSimpleCostOptimization fn = do
  ann <- (M.! fn) <$> use sig
  let cost = ctxSymbolicCost (withCost ann)
  let costTerm = sum $ map (sum . M.elems . opCoeffs) $ M.elems cost
  optiTargets %= (costTerm:)

  
addFullCostOptimization :: Id -> ProveMonad ()
addFullCostOptimization fn = do
  ann <- (M.! fn) <$> use sig
  let (q, q') = withCost ann
  costTerm <- ctxCOptimize q q'
  optiTargets %= (costTerm:)

argsWithPot :: (Map Type [Id], Map Type [Id]) -> ProveMonad (Map Type [Id], Map Type [Id])
argsWithPot (from, to) = do
  pots <- use potentials
  let from' = M.restrictKeys from $ M.keysSet pots
  let to' = M.restrictKeys to $ M.keysSet pots
  return (from', to')

genFunRsrcAnn :: PositionedFunDef -> ProveMonad CostAnalysis.RsrcAnn.FunRsrcAnn
genFunRsrcAnn fn@(FunDef funAnn _ _ _) = do
  (argsFrom, argsTo) <- argsWithPot $ fnArgsByType fn
  pots <- use potentials
  to <- if hasPotential fn then
          return $ M.mapWithKey (\t _ -> annForType t pots) argsTo
        else if null argsTo then
               emptyAnnCtx (M.map (const []) argsFrom) "Q'" "fn" 
             else
               emptyAnnCtx argsTo "Q'" "fn" 

  let numCfSigs = fromMaybe 1 $ tfNumCf funAnn
  from <- defaultAnnCtx argsFrom "Q" "fn" 
  fromCfs <- mapM (const $ defaultAnnCtx argsFrom "P" "fn cf") [1..numCfSigs]
  toCfs <- mapM (const $ defaultAnnCtx argsTo "P'" "fn cf") [1..numCfSigs]
  return $ FunRsrcAnn (from, to) (zip fromCfs toCfs) (hasPotential fn)

  
addSigCs :: [Id] -> Solution -> ProveMonad ()
addSigCs fns solution = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  let cs = concatMap go (getCoeffs sig')
  sigCs %= (++cs)
  where go coeff = eq (CoeffTerm coeff) (ConstTerm (solution M.! coeff))

argsForRHS :: [FunDef Positioned] -> [Type] -> ProveMonad (Map Type [Id])
argsForRHS fns ts = M.fromList <$> mapM checkArgs ts
  where checkArgs :: Type -> ProveMonad (Type, [Id])
        checkArgs t = do
          let args = mapMaybe (M.!? t) rhsArgsByType
          if sameLength args then
            case args of
              [] -> return (t, [])
              sample:_ -> return (t, sample)
          else throwError $ DerivErr $ SourceError (tfLoc $ funAnn (head fns))
               "Cost analysis requries all involved functions to have the same return type to guarantee a consistent potential function."
        rhsArgsByType :: [Map Type [Id]]
        rhsArgsByType = [ snd $ fnArgsByType fn
                        | fn <- fns,
                          hasPotential fn]
        sameLength l = and [length l1 == length l2
                           | l1 <- l, l2 <- l]

