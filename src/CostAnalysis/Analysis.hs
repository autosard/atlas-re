{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

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
import CostAnalysis.Constraint hiding (and, sum)
import qualified CostAnalysis.Constraint as C
import SourceError
import CostAnalysis.Rules
import Control.Monad.Except (MonadError (throwError))
import CostAnalysis.Deriv
import CostAnalysis.Coeff
import Typing.Type
import CostAnalysis.Potential(PotFnMap, Potential (cExternal), auxSigs)
import CostAnalysis.Potential.Kind (fromKind)
import Control.Monad.Extra (concatMapM, ifM, mapAndUnzipM)
import CostAnalysis.Template (TermTemplate, FreeTemplate,
                              defaultTemplOpts,
                              TemplateOptions(..))
import CostAnalysis.Predicate(potForMeasure)
import CostAnalysis.Annotation 
import CostAnalysis.ProveMonad 

defaultPotentialMap = M.fromList
  [
    (ListType, Polynomial),
    (TreeType, LogLR)
  ]


initPotentials :: PositionedModule -> Map Type PotentialKind -> ProveMonad PotFnMap
initPotentials mod kinds = do 
  potFnArgs <- argsForRHS (M.elems $ defs mod) (M.keys kinds)
  M.fromList <$> mapM go (M.toAscList potFnArgs)
  where go (t, args) = do
          let pot = fromKind (kinds M.! t)
          potFn <- defaultTemplFor pot "Q'" "potFn" args
          return (t, (pot, potFn))

data AnalysisResult = AnalysisResult
  Derivation
  [Constraint]
  FreeSignature
  (Either [Constraint] (Solution, PotFnMap))

analyzeModule :: ProofEnv -> PositionedModule
  -> IO (Either SourceError AnalysisResult)
analyzeModule env mod = do
  let state = ProofState M.empty [] [] 0 0 [] [] M.empty M.empty M.empty False
              (FnConfig AmortizedCost (Just 1) False)
  (result, state', solution) <- runProof env state (analyzeModule' mod)
  let deriv = T.Node (ProgRuleApp mod) (state'^.fnDerivs)
  case result of
    Left (DerivErr srcErr) -> return (Left srcErr)
    Left (UnsatErr core) -> return (Right (AnalysisResult
                                            deriv
                                            (state'^.sigCs)
                                            (state'^.sig)
                                            (Left core)))
    Right _ -> return (Right (AnalysisResult
                               deriv
                               (state'^.sigCs)
                               (state'^.sig)
                               (Right (solution, state'^.potentials))))



analyzeModule' :: PositionedModule -> ProveMonad ()
analyzeModule' mod = do
  pots <- initPotentials mod $ (modPotMap . config) mod `M.union` defaultPotentialMap
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
  ann <- genFunAnn fn
  sig %= M.insert id ann
  analyzeFn' fn

analyzeFn' :: PositionedFunDef -> ProveMonad Derivation
analyzeFn' def@(FunDef funAnn fnId _ body) = do
  mode <- view analysisMode

  assertNonNegativePotFn fnId
  
  case mode of
    CheckCoefficients -> case tfCostAnn funAnn of
      Just (Coeffs target) -> coeffsMatchAnnotation fnId target
      Just (Cost cost) -> coeffsMatchAnnotation fnId 
        (FunAnn (CostSig
                 (FunSig (cost, M.empty) M.empty)
                 Nothing) [] M.empty)
      _noCoeff -> errorFrom (SynExpr body) "Missing resource coefficient annotation for check-coeffs mode."
    -- CheckCost -> case tfCostAnn funAnn of
    --   Just (Cost cost) -> cmpCostWithAnn assertEq fnId cost
    --   _noCost -> errorFrom (SynExpr body) "Missing cost annotation for check-cost mode."
    -- ImproveCost -> case tfCostAnn funAnn of
    --   Just (Cost _ cost) -> do
    --     cmpCostWithAnn assertLe fnId cost
    --     addSimpleCostOptimization fnId
    --   noCost_ -> errorFrom (SynExpr body) "Missing cost annotation for improve-cost mode."
    Infer -> do
      s <- use sig
      let CostSig s1 s2 = withCost $ s M.! fnId
      tellSigCs =<< externalCsForCtx s1
      tellSigCs =<< maybe (return []) externalCsForCtx s2
      rhs <- view rhsTerms
      let hybrid = (costMode . tfFnConfig) funAnn == HybridCost
      addFullCostOptimization fnId True -- (rhs || hybrid)
  proveFun def

externalCsForCtx :: FunSig FreeTemplate -> ProveMonad [Constraint]
externalCsForCtx (FunSig (q, qe) q') = concatMapM csForType (M.assocs q) 
  where csForType :: (Type, FreeTemplate) -> ProveMonad [Constraint]
        csForType (t, q) = do
          pots <- use potentials
          if M.member t q' then do
            pot <- potForType t 
            return $ cExternal pot q (q' M.! t)
          else
            return []

assertNonNegativePotFn :: Id -> ProveMonad ()
assertNonNegativePotFn fn = do
  ann <- (M.! fn) <$> use sig
  let CostSig s1 s2 = withCost ann
  potGeZero s1
  case s2 of
    Just s -> potGeZero s
    Nothing -> tellSigCs []
  where potGeZero (FunSig (_,_) q') = do
          tellSigCs $ assertGeZero q'

-- assertNonNegativeCost' :: Id -> ProveMonad ()
-- assertNonNegativeCost' fn = do
--   ann <- (M.! fn) <$> use sig
--   let (FunSig (q,qe) q') = withCost ann
--   let cost = symbolicCost ((q,qe), q')
--   let zero = zeroAnnFrom cost
--   cs <- annFarkas (S.fromList [Mono]) S.empty zero cost
--   tellSigCs cs

-- assertNonNegativeCost :: Id -> ProveMonad ()
-- assertNonNegativeCost fn = do
--   ann <- (M.! fn) <$> use sig
--   let (FunSig (q,qe) q') = withCost ann
--   let cost = symbolicCost ((q,qe), q')
--   tellSigCs (assertGeZero cost)

type CostComparision = Map Type TermTemplate -> BoundAnn -> [Constraint]

-- cmpCostWithAnn :: CostComparision -> Id -> BoundAnn -> ProveMonad ()
-- cmpCostWithAnn cmp fn costAnn = do
--   ann <- (M.! fn) <$> use sig
--   let (FunSig (q,qe) q') = withCost ann
--   let cost = symbolicCost ((q,qe), q')
--   tellSigCs $ assertGeZero cost
--   tellSigCs $ cmp cost costAnn

coeffsMatchAnnotation :: Id -> BoundFunAnn -> ProveMonad ()
coeffsMatchAnnotation fn target = do
  ann <- (M.! fn) <$> use sig
  tellSigCs $ assertFunAnnEq ann target

-- addSimpleCostOptimization :: Id -> ProveMonad ()
-- addSimpleCostOptimization fn = do
--   ann <- (M.! fn) <$> use sig
--   let (FunSig (q,qe) q') = withCost ann
--   let cost = symbolicCost ((q,qe), q')
--   let costTerm = sum cost
--   optiTargets %= (costTerm:)

  
addFullCostOptimization :: Id -> Bool -> ProveMonad ()
addFullCostOptimization fn addAbs = do
  ann <- (M.! fn) <$> use sig
  let CostSig s1 s2 = withCost ann
  optimize s1
  case s2 of
    Just s -> optimize s
    Nothing -> tellSigCs []
  where optimize (FunSig (q, qe) q')  = do
          costTerms <- annCOptimize (q, qe) q'
          absTerms <- if addAbs 
                      then mapM abs costTerms
                      else return []
          let costTerm = C.sum $ costTerms ++ absTerms
          optiTargets %= (costTerm:)
        abs :: Term -> ProveMonad Term
        abs t = do
          absT <- freshVar 
          tellCs $ 
            ge absT t
            ++ ge absT (minus t)
          return absT
            

argsWithPot :: (Map Type [Id], Map Type [Id]) -> ProveMonad (Map Type [Id], Map Type [Id])
argsWithPot (from, to) = do
  pots <- use potentials
  let from' = M.restrictKeys from $ M.keysSet pots
  let to' = M.restrictKeys to $ M.keysSet pots
  return (from', to')

genFunAnn :: PositionedFunDef -> ProveMonad FreeFunAnn
genFunAnn fn@(FunDef funAnn _ _ _) = do
  (argsFrom, argsTo) <- argsWithPot $ fnArgsByType fn
  pots <- use potentials
  let potFnAnn = M.mapWithKey (\t _ -> annForType t pots) argsTo
  costSig <- do
    fromPrimary <- defaultAnn argsFrom "Q" "fn"
    fromPrimaryRef <- ifM (view rhsTerms)
                      (defaultAnn argsTo "QE" "fn")
                      (emptyAnn (M.map (,[]) argsTo) "QE" "fn")
    zero <- if null argsTo
                then defaultAnn (M.map (const []) argsFrom) "Q'" "fn" 
                else defaultAnn argsTo "Q' zero" "fn"
    tellSigCs $ assertZero zero                  
    case (costMode . tfFnConfig) funAnn of
      AmortizedCost -> do
        let to = potFnAnn
        return $ CostSig (FunSig
                           (fromPrimary, fromPrimaryRef)
                           to)
                         Nothing
      WorstCaseCost -> do
        return $ CostSig (FunSig
                           (fromPrimary, fromPrimaryRef)
                           zero)
                         Nothing
      HybridCost -> do
        let toPrimary = potFnAnn
        fromSecondary <- defaultAnn argsFrom "Q" "fn"
        fromRefSecondary <- ifM (view rhsTerms)
                            (defaultAnn argsTo "QE" "fn")
                            (emptyAnn (M.map (,[]) argsTo) "QE" "fn")
        let toSecondary = zero
        return $ CostSig (FunSig (fromPrimary, fromPrimaryRef) toPrimary)
                         (Just (FunSig (fromSecondary, fromRefSecondary) toSecondary))
  
  let numCfSigs = fromMaybe 1 $ (numCf . tfFnConfig) funAnn
  (fromCfs, toCfs) <- mapAndUnzipM (const $ genCf argsFrom argsTo) [1..numCfSigs]
  auxs <- M.fromList . concat <$> mapM (genAuxs argsFrom argsTo) (M.assocs pots)
  return $ FunAnn
    costSig
    (Prelude.zipWith FunSig fromCfs toCfs)
    auxs
  where genCf argsFrom argsTo = do
          let opts = defaultTemplOpts {ghostVars=True}
          q <- freshAnn argsFrom "P" "fn cf" opts
          qe <- ifM (view rhsTerms)
            (freshAnn argsTo "PE" "fn cf" opts)
            (emptyAnn (M.map (,[]) argsTo) "PE" "fn cf")
          q' <- freshAnn argsTo "P'" "fn cf" opts
          return ((q, qe), q')
        genAux argsFrom argsTo t m = do
          let pot = (fromKind . potForMeasure) m
          auxPotentials . at t ?= pot
          q <- singleAnn pot t argsFrom "A" "fn aux"
          qe <- ifM (view rhsTerms)
            (defaultAnn argsTo "AE" "fn aux")
            (emptyAnn (M.map (,[]) argsTo) "AE" "fn aux")
          q' <- singleAnn pot t argsTo "A'" "fn aux"
          return (FunSig (q, qe) q')
        genAuxs argsFrom argsTo (t, (pot, _)) = do
          mapM (\(m, k) -> ((m,k), ) <$> genAux argsFrom argsTo t m) (auxSigs pot)
          


addSigCs :: [Id] -> Solution -> ProveMonad ()
addSigCs fns (solution, _) = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  let cs = concatMap go (getCoeffs sig')
  sigCs %= (++cs)
  where go coeff = eq (CoeffTerm coeff) (ConstTerm (fromMaybe 0 (solution M.!? coeff)))

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
                          let mode = (costMode . tfFnConfig . funAnn) fn,
                          mode == AmortizedCost || mode == HybridCost]
        sameLength l = and [length l1 == length l2
                           | l1 <- l, l2 <- l]

