{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module CostAnalysis.Analysis where

import Prelude hiding (sum, (!?))
import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Micro.Platform

import System.Exit (die)

import Primitive(Id, prettyPrint, dbg)
import Syntax.Ast
import CostAnalysis.Solving (solve)
import CostAnalysis.Constraint hiding (and, sum)
import SourceError
-- import CostAnalysis.Rules
import Control.Monad.Except (MonadError (throwError))
import CostAnalysis.Deriv
import Typing.Type
import Typing.Scheme (tFunArgs, tFunResult, findByType)
import Syntax.Measure (SizeTransform)
-- import CostAnalysis.Potential(PotFnMap, Potential (cExternal), auxSigs)
-- import CostAnalysis.Potential.Kind (fromKind)

import CostAnalysis.Template
import CostAnalysis.TemplateLanguage
import CostAnalysis.ProveMonad
import CostAnalysis.Rules (JudgementType (..))
import Syntax.ResourceExpression
import Control.Monad (unless, when)
import Data.Maybe (isNothing)
import Syntax.ResourceExpression.Order (computeStratifiedCosts)
import CostAnalysis.Constraint (sum)
import CostAnalysis.Coeff (Coeff(Coeff))
import Control.Monad.Extra (ifM, whenM)


data AnalysisResult = AnalysisResult {
  _arDerivs :: Map Id [Derivation]
  , _arSig :: Map Id FreeSig
  , _arSigCs :: [Formula]
  , _arSizeSig :: Map Id SizeTransform
  , _arResult :: Either [Formula] Solution
  } deriving Show

analyzeProgram :: ProofEnv -> Program Positioned
  -> IO AnalysisResult
analyzeProgram env prog = do
  let state = ProofState {
        _sig = M.empty
        , _sizeSig = M.empty
        , _sigCs = []
        , _tLang = defaultTLang
        , _optiTargets = []
        , _annIdGen = 0
        , _varIdGen = 0
        , _constraints = []
        , _fnDerivs = M.empty
        , _solution = Nothing
        , _measureSig = M.empty
        }

  (result, state', solution) <- runProof env state (analyzeStages prog)
  
  case result of
    Left (DerivErr srcErr) -> printSrcError srcErr
    Left (UnsatErr core) -> buildResult state' (Left core)
    Left (MissingMeasure t m) -> die $ "Missing definition of measure '" ++ show m ++ "' for type '" ++ prettyPrint t ++ "'."  
    Right _ -> buildResult state' (Right solution)
  where buildResult state result =
          return $ (AnalysisResult
                     (state^.fnDerivs)
                     (state^.sig)
                     (state^.sigCs)
                     (state^.sizeSig)
                     result)
          

analyzeStages :: Program Positioned -> ProveMonad ()
analyzeStages prog = do
  analyzeSize prog

  resetAnalysis
  analyzeCost prog

analyzeSize :: Program Positioned -> ProveMonad ()
analyzeSize prog = do
  tLang .= sizeTLang
  initSig prog
  constrainSigForSize prog
  optimizeSig prog
  analyzeProg CfEq prog

  obtainSizeTransforms

analyzeCost :: Program Positioned -> ProveMonad ()
analyzeCost prog = do
  let lang = fromConfig $ templateConfig (prog^.pConfig)
  tLang .= lang
  initSig prog
  constrainSig prog
  optimizeSig prog
  analyzeProg Standard prog
  
initSig :: Program Positioned -> ProveMonad ()
initSig prog = do
  computedSigs <- M.traverseWithKey genSig (prog^.pSig)
  sig .= computedSigs

  mSig' <- enrichMeasureSig (prog^.pMeasureSig)
  measureSig .= mSig'
  where genSig :: Id -> FunSig -> ProveMonad FreeSig
        genSig fn sig = do
          let argts = tFunArgs (sig^.typeSig)
              args = ((prog^.pFunDefs) M.! fn)^.funArgs
              argsWithT = zip args argts
          tl <- use tLang
          from <- freshTempl [x | (x,t) <- argsWithT, isResourceRelevant t]
          
          let binder = maybe "𝜈" csBinder (sig^.costSig) 
          to <- freshTempl [binder]
          return $ FreeSig from to binder args

analyzeProg :: JudgementType -> Program Positioned ->  ProveMonad ()
analyzeProg mode prog = do
  incr <- view incremental 
  if incr then
    mapM_ (analyzeBindingGroup mode prog) ( prog^.pMutRecGroups)
  else
    analyzeBindingGroup mode prog (concat $ prog^.pMutRecGroups)

analyzeBindingGroup :: JudgementType -> Program Positioned -> [Id]  -> ProveMonad ()
analyzeBindingGroup mode prog fns = do
  mapM_ go fns
  sol <- solve fns
  tell sol
  solution .= Just (fst sol)
  where go :: Id -> ProveMonad ()
        go fn = whenM (sizeTransformable prog fn) $ do
          let def = (prog^.pFunDefs) M.! fn
          let sig = (prog^.pSig) M.! fn
          deriv <- proveFun sig def mode
          appendDeriv fn deriv

constrainSigForSize :: Program Positioned -> ProveMonad ()
constrainSigForSize prog = do
  fs <- use sig
  mapM_ go $ M.toList fs 
  where go :: (Id, FreeSig) -> ProveMonad ()
        go (fn, fs) = do
          whenM (sizeTransformable prog fn) $ do
            let sizeOne = BoundTemplate $ M.singleton (RTSize (fs^.fsBinder)) 1
            tellSigCs $ assertEq sizeOne (fs^.fsTo)
        
optimizeSig :: Program Positioned -> ProveMonad ()
optimizeSig prog = mapM_ go . M.toList =<< use sig
  where go :: (Id, FreeSig) -> ProveMonad ()
        go (fn, fsSig) = do
          whenM (sizeTransformable prog fn) $
            optiTargets %= (costTerm:)
          where
            templ = fsSig^.fsFrom
            termsWithCost = computeStratifiedCosts [] (templ^.ftTerms)
            costTerm = sum [prod2 (ConstTerm (fromIntegral c)) (CoeffTerm (Coeff (templ^.ftId) t))
                           | (t, c) <- termsWithCost]
        

constrainSig :: Program Positioned -> ProveMonad ()
constrainSig prog = do
  mode <- view analysisMode
  case mode of
    Check -> assertSigMatchesAnn prog
    Infer -> assertPotential
    -- Infer -> do
    --   s <- use sig
    --   let CostSig s1 s2 = withCost $ s M.! fnId
    --   tellSigCs =<< externalCsForCtx s1
    --   tellSigCs =<< maybe (return []) externalCsForCtx s2
    --   rhs <- view rhsTerms
    --   let hybrid = (costMode . tfFnConfig) funAnn == HybridCost
    --   addFullCostOptimization fnId True -- (rhs || hybrid)

assertPotential :: ProveMonad ()
assertPotential = mapM_ go =<< use sig
  where go :: FreeSig -> ProveMonad ()
        go fs = do
          let fromCs = concat [(fs^.fsFrom)!?RTPhi x `eq` ConstTerm 1 | x <- args (fs^.fsFrom)]
          let toCs = concat [case t of
                               i@(RTPhi _) -> (fs^.fsTo)!i `eq` ConstTerm 1
                               i -> zero ((fs^.fsTo)!i)
                            | t <- S.toList $ terms (fs^.fsTo)]
          tellSigCs (fromCs ++ toCs)


assertSigMatchesAnn :: Program Positioned -> ProveMonad ()
assertSigMatchesAnn prog = do
  M.traverseWithKey go (prog^.pSig)
  return ()
        where go :: Id -> FunSig -> ProveMonad ()
              go fn fsig = case fsig^.costSig of
                Just cs -> do
                  fs <- (M.! fn) <$> use sig
                  tellSigCs $ assertEqVarsSubst (args (fs^.fsFrom)) (args (csFrom cs))  (fs^.fsFrom) (csFrom cs) 
                  tellSigCs $ assertEqVarsSubst [fs^.fsBinder] [csBinder cs]  (fs^.fsTo) (csTo cs) 
                Nothing -> throwError $ ProofErr ("Missing resource annotation for function"
                                                  ++ " '" ++ show fn ++ "'"
                                                  ++ " in check mode.")

obtainSizeTransforms :: ProveMonad ()
obtainSizeTransforms = do
  fsSig <- use sig
  mapM_ go $ M.toList fsSig
  where go :: (Id, FreeSig) -> ProveMonad ()
        go (fn, fs) = do
          sol <- use solution
          case sol of
            Just sol -> do
              let boundTempl = bindTemplate (fs^.fsFrom) sol
              let transform = sizeTransformFromTempl (fs^.fsFormArgs) boundTempl
              sizeSig . at fn .= Just transform
            Nothing -> error "cannot obtain size transforms without a solution."
  

appendDeriv :: Id -> Derivation -> ProveMonad ()
appendDeriv fn newDeriv = 
  fnDerivs . at fn %= \case
    Nothing     -> Just [newDeriv]
    Just derivs -> Just (derivs ++ [newDeriv]) 


-- externalCsForCtx :: FunSig FreeTemplate -> ProveMonad [Constraint]
-- externalCsForCtx (FunSig (q, qe) q') = concatMapM csForType (M.assocs q) 
--   where csForType :: (Type, FreeTemplate) -> ProveMonad [Constraint]
--         csForType (t, q) = do
--           pots <- use potentials
--           if M.member t q' then do
--             pot <- potForType t 
--             return $ cExternal pot q (q' M.! t)
--           else
--             return []

-- assertNonNegativePotFn :: Id -> ProveMonad ()
-- assertNonNegativePotFn fn = do
--   ann <- (M.! fn) <$> use sig
--   let CostSig s1 s2 = withCost ann
--   potGeZero s1
--   case s2 of
--     Just s -> potGeZero s
--     Nothing -> tellSigCs []
--   where potGeZero (FunSig (_,_) q') = do
--           tellSigCs $ assertGeZero q'

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

-- type CostComparision = Map Type TermTemplate -> BoundAnn -> [Constraint]

-- cmpCostWithAnn :: CostComparision -> Id -> BoundAnn -> ProveMonad ()
-- cmpCostWithAnn cmp fn costAnn = do
--   ann <- (M.! fn) <$> use sig
--   let (FunSig (q,qe) q') = withCost ann
--   let cost = symbolicCost ((q,qe), q')
--   tellSigCs $ assertGeZero cost
--   tellSigCs $ cmp cost costAnn

-- coeffsMatchAnnotation :: Id -> BoundFunAnn -> ProveMonad ()
-- coeffsMatchAnnotation fn target = do
--   ann <- (M.! fn) <$> use sig
--   tellSigCs $ assertFunAnnEq ann target

-- addSimpleCostOptimization :: Id -> ProveMonad ()
-- addSimpleCostOptimization fn = do
--   ann <- (M.! fn) <$> use sig
--   let (FunSig (q,qe) q') = withCost ann
--   let cost = symbolicCost ((q,qe), q')
--   let costTerm = sum cost
--   optiTargets %= (costTerm:)

  
-- addFullCostOptimization :: Id -> Bool -> ProveMonad ()
-- addFullCostOptimization fn addAbs = do
--   ann <- (M.! fn) <$> use sig
--   let CostSig s1 s2 = withCost ann
--   optimize s1
--   case s2 of
--     Just s -> optimize s
--     Nothing -> tellSigCs []
--   where optimize (FunSig (q, qe) q')  = do
--           costTerms <- annCOptimize (q, qe) q'
--           absTerms <- if addAbs 
--                       then mapM abs costTerms
--                       else return []
--           let costTerm = C.sum $ costTerms ++ absTerms
--           optiTargets %= (costTerm:)
--         abs :: Term -> ProveMonad Term
--         abs t = do
--           absT <- freshVar 
--           tellCs $ 
--             ge absT t
--             ++ ge absT (minus t)
--           return absT
            

-- argsWithPot :: (Map Type [Id], Map Type [Id]) -> ProveMonad (Map Type [Id], Map Type [Id])
-- argsWithPot (from, to) = do
--   pots <- use potentials
--   let from' = M.restrictKeys from $ M.keysSet pots
--   let to' = M.restrictKeys to $ M.keysSet pots
--   return (from', to')

-- genFunAnn :: PositionedFunDef -> ProveMonad FreeFunAnn
-- genFunAnn fn@(FunDef funAnn _ _ _) = do
--   (argsFrom, argsTo) <- argsWithPot $ fnArgsByType fn
--   pots <- use potentials
--   let potFnAnn = M.mapWithKey (\t _ -> annForType t pots) argsTo
--   costSig <- do
--     fromPrimary <- defaultAnn argsFrom "Q" "fn"
--     fromPrimaryRef <- ifM (view rhsTerms)
--                       (defaultAnn argsTo "QE" "fn")
--                       (emptyAnn (M.map (,[]) argsTo) "QE" "fn")
--     zero <- if null argsTo
--                 then defaultAnn (M.map (const []) argsFrom) "Q'" "fn" 
--                 else defaultAnn argsTo "Q' zero" "fn"
--     tellSigCs $ assertZero zero                  
--     case (costMode . tfFnConfig) funAnn of
--       AmortizedCost -> do
--         let to = potFnAnn
--         return $ CostSig (FunSig
--                            (fromPrimary, fromPrimaryRef)
--                            to)
--                          Nothing
--       WorstCaseCost -> do
--         return $ CostSig (FunSig
--                            (fromPrimary, fromPrimaryRef)
--                            zero)
--                          Nothing
--       HybridCost -> do
--         let toPrimary = potFnAnn
--         fromSecondary <- defaultAnn argsFrom "Q" "fn"
--         fromRefSecondary <- ifM (view rhsTerms)
--                             (defaultAnn argsTo "QE" "fn")
--                             (emptyAnn (M.map (,[]) argsTo) "QE" "fn")
--         let toSecondary = zero
--         return $ CostSig (FunSig (fromPrimary, fromPrimaryRef) toPrimary)
--                          (Just (FunSig (fromSecondary, fromRefSecondary) toSecondary))
  
--   let numCfSigs = fromMaybe 1 $ (numCf . tfFnConfig) funAnn
--   (fromCfs, toCfs) <- mapAndUnzipM (const $ genCf argsFrom argsTo) [1..numCfSigs]
--   auxs <- M.fromList . concat <$> mapM (genAuxs argsFrom argsTo) (M.assocs pots)
--   return $ FunAnn
--     costSig
--     (Prelude.zipWith FunSig fromCfs toCfs)
--     auxs
--   where genCf argsFrom argsTo = do
--           let opts = defaultTemplOpts {ghostVars=True}
--           q <- freshAnn argsFrom "P" "fn cf" opts
--           qe <- ifM (view rhsTerms)
--             (freshAnn argsTo "PE" "fn cf" opts)
--             (emptyAnn (M.map (,[]) argsTo) "PE" "fn cf")
--           q' <- freshAnn argsTo "P'" "fn cf" opts
--           return ((q, qe), q')
--         genAux argsFrom argsTo t m = do
--           let pot = (fromKind . potForMeasure) m
--           auxPotentials . at t ?= pot
--           q <- singleAnn pot t argsFrom "A" "fn aux"
--           qe <- ifM (view rhsTerms)
--             (defaultAnn argsTo "AE" "fn aux")
--             (emptyAnn (M.map (,[]) argsTo) "AE" "fn aux")
--           q' <- singleAnn pot t argsTo "A'" "fn aux"
--           return (FunSig (q, qe) q')
--         genAuxs argsFrom argsTo (t, (pot, _)) = do
--           mapM (\(m, k) -> ((m,k), ) <$> genAux argsFrom argsTo t m) (auxSigs pot)
          


-- addSigCs :: [Id] -> Solution -> ProveMonad ()
-- addSigCs fns (solution, _) = do
--   sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
--   let cs = concatMap go (getCoeffs sig')
--   sigCs %= (++cs)
--   where go coeff = eq (CoeffTerm coeff) (ConstTerm (fromMaybe 0 (solution M.!? coeff)))

-- argsForRHS :: [FunDef Positioned] -> [Type] -> ProveMonad (Map Type [Id])
-- argsForRHS fns ts = M.fromList <$> mapM checkArgs ts
--   where checkArgs :: Type -> ProveMonad (Type, [Id])
--         checkArgs t = do
--           let args = mapMaybe (M.!? t) rhsArgsByType
--           if sameLength args then
--             case args of
--               [] -> return (t, [])
--               sample:_ -> return (t, sample)
--           else throwError $ DerivErr $ SourceError (tfLoc $ funAnn (head fns))
--                "Cost analysis requries all involved functions to have the same return type to guarantee a consistent potential function."
--         rhsArgsByType :: [Map Type [Id]]
--         rhsArgsByType = [ snd $ fnArgsByType fn
--                         | fn <- fns,
--                           let mode = (costMode . tfFnConfig . funAnn) fn,
--                           mode == AmortizedCost || mode == HybridCost]
--         sameLength l = and [length l1 == length l2
--                            | l1 <- l, l2 <- l]

