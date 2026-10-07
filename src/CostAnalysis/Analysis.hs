{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

module CostAnalysis.Analysis
  ( analyzeProgram
  , AnalysisResult (..)
  ) where

import Prelude hiding (sum, (!?))
import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Micro.Platform

import System.Exit (die)

import Syntax (Id, Positioned)
import Syntax.PrettyPrint (prettyPrint)              
import Syntax.Program
import CostAnalysis.Solving (solve)
import CostAnalysis.Constraint hiding (and, sum)
import SourceError
import Control.Monad.Except (MonadError (throwError, catchError))
import CostAnalysis.Deriv ( derivFun )
import Syntax.Types.Type
import Syntax.Types.Scheme (tFunArgs, Scheme(..), fnArgType, tFunResult)
import Syntax.Measure (SizeTransform, ConstPat (..), Relation, MeasureAlgebra (..))

import CostAnalysis.Template
import CostAnalysis.TemplateLanguage
import CostAnalysis.ProveMonad
import CostAnalysis.Rules (JudgementType (..), SubArg (..))
import CostAnalysis.Subtyping (templNonNeg)
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Order (stratifiedWeights)
import CostAnalysis.Constraint (sum)
import CostAnalysis.Coeff (Coeff(Coeff))
import Control.Monad.Extra (whenM, filterM, forM_, forM)
import qualified Syntax.Measure (Relation(..))
import Syntax.ResourceExpression.Inequality (sizeConstraints)


data AnalysisResult = AnalysisResult {
  _arDerivs :: Map Id [Derivation]
  , _arSig :: Map Id FreeSig
  , _arSigCs :: [Formula]
  , _arSizeSig :: Map Id SizeTransform
  , _arResult :: Either [Formula] Solution
  , _arPotSig :: Map Scheme [(ConstPat, ResourceExpr)]
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
          return $ AnalysisResult
                     (state^.fnDerivs)
                     (state^.sig)
                     (state^.sigCs)
                     (state^.sizeSig)
                     result
                     (potentials $ state^.measureSig)



analyzeStages :: Program Positioned -> ProveMonad ()
analyzeStages prog = do
  tLang .= fromConfig (templateConfig $ prog^.pConfig)
  initMeasureSig prog
  potOptiTgts <- use optiTargets
  -- constraints of the optimisation targets for inferred potentials (|q| >= +-q);
  -- they would otherwise be lost by the solving and reset of the size analysis
  potCs <- use constraints
  
  analyzeSize prog

  resetAnalysis
  optiTargets .= potOptiTgts
  tellSigCs potCs
  analyzeCost prog

analyzeSize :: Program Positioned -> ProveMonad ()
analyzeSize prog = do
  tLang .= sizeTLang
  initSizeSig prog
  constrainSigForSize prog
  
  mapM_ analyzeScc ( prog^.pMutRecGroups)

  where analyzeScc scc = do
          optimizeScc scc prog
          (do
              strictPass scc
              trackSolution
              obtainSizeTransforms scc Syntax.Measure.Eq
           ) `catchError` (\e -> case e of
                (UnsatErr _)  -> do
                  constraints .= []
                  catchError (do
                                 upperBoundPass scc
                                 trackSolution
                                 obtainSizeTransforms scc Syntax.Measure.Ge
                             ) $
                    \case (UnsatErr _) -> return ()
   
                e -> throwError e)
           
        strictPass = analyzeBindingGroup CfEq prog 
        upperBoundPass = analyzeBindingGroup Cf prog
        trackSolution = do
          (Just coeffs) <- use solution
          tellSigCs $ concatMap (\(q, v) -> eq (CoeffTerm q) (ConstTerm v)) (M.toList coeffs)


analyzeCost :: Program Positioned -> ProveMonad ()
analyzeCost prog = do
  tLang .= fromConfig (templateConfig (prog^.pConfig))
  initCostSig prog
  constrainSig prog
  whenM (view inferPotential) $ constrainPotMeasures prog
  
  analyzeProg Standard prog

-- | Inferred potential measures must be non-negative. By induction on values it
-- suffices that the right-hand side of every equation is non-negative,
-- assuming the potentials of the fields are, i.e. 0 <=_K e for every equation.
constrainPotMeasures :: Program Positioned -> ProveMonad ()
constrainPotMeasures prog = do
  mSig <- use measureSig
  forM_ (M.toList mSig) $ \(scheme, env) -> do
    let fields = M.fromList $ ctorFields (prog^.pDataEnv) scheme
        (Equations eqs) = emPotentialMeasure env
    forM_ eqs $ \(ConstPat cName _, rhs) -> do
      rctx <- addVarConstraints (M.findWithDefault [] cName fields) []
      cs <- templNonNeg (S.fromList [Mono, L2xy]) rctx
              (ArithTemplate (M.map fromRScalar rhs))
      tellSigCs cs

initMeasureSig :: Program Positioned -> ProveMonad ()
initMeasureSig prog = do
  mSig' <- enrichMeasureSig prog
  measureSig .= mSig'

initSizeSig :: Program Positioned -> ProveMonad ()
initSizeSig prog = initSig' (sizeTransformable prog) prog

initCostSig = initSig' (\_ -> return True) 


initSig' :: (Id -> ProveMonad Bool) -> Program Positioned -> ProveMonad ()
initSig' filter prog = do
  validFns <- filterM filter $ M.keys (prog^.pSig)
  let filteredSig = M.restrictKeys (prog^.pSig) (S.fromList validFns)
  computedSigs <- M.traverseWithKey (genSig prog) filteredSig 
  sig .= computedSigs

  
  
genSig :: Program Positioned -> Id -> FunSig -> ProveMonad FreeSig
genSig prog fn sig = do
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
    analyzeBindingGroup mode prog (concat (prog^.pMutRecGroups))

analyzeBindingGroup :: JudgementType -> Program Positioned -> [Id]  -> ProveMonad ()
analyzeBindingGroup mode prog fns = do
  mapM_ go fns
  sol <- solve mode fns
  tell sol
  solution .= Just (fst sol)
  where go :: Id -> ProveMonad ()
        go fn = whenM (M.member fn <$> use sig) $ do
          let def = (prog^.pFunDefs) M.! fn
          let sig = (prog^.pSig) M.! fn
          deriv <- derivFun sig def mode
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
        
optimizeSigs :: Program Positioned -> ProveMonad ()
optimizeSigs prog = mapM_ (optimizeSig prog) . M.toList =<< use sig

optimizeScc :: [Id] -> Program Positioned -> ProveMonad ()
optimizeScc scc prog = do
  sig' <- (`M.restrictKeys` S.fromList scc) <$> use sig
  mapM_ (optimizeSig prog) $ M.toList sig'

optimizeSig :: Program Positioned -> (Id, FreeSig) -> ProveMonad () 
optimizeSig prog (fn, fsSig) = do
  guards <- sizeConstraints <$> addVarConstraints argsWithTypes []
  let termsWithCost = stratifiedWeights guards terms'
  let costTerm = sum [prod2 (ConstTerm w) (CoeffTerm (Coeff (templ^.ftId) t))
                 | (t, w) <- termsWithCost]
  whenM (sizeTransformable prog fn) $
    optiTargets %= (costTerm:)
  where
    templ = fsSig^.fsFrom
    terms' = S.filter (not . isZero) (templ^.ftTerms)
    funDef = (prog^.pFunDefs) M.! fn
    fnTSig = ((prog^.pSig) M.! fn)^.typeSig
    argsWithTypes = zip (funDef^.funArgs) (tFunArgs fnTSig)
        

constrainSig :: Program Positioned -> ProveMonad ()
constrainSig prog = do
  mode <- view analysisMode
  case mode of
    Check -> assertSigMatchesAnn prog
    Infer -> do
      assertPotential prog
      optimizeSigs prog

assertPotential :: Program Positioned -> ProveMonad ()
assertPotential p = mapM_ go . M.toList =<< use sig
  where go :: (Id, FreeSig) -> ProveMonad ()
        go (fn, fs) = do
          costMode <- M.findWithDefault Amortized fn <$> view costModes

          let tFun = p ^. pSig . singular (ix fn) . typeSig
          let returnType = tFunResult tFun
          let pot = case costMode of
                WorstCase -> ConstTerm 0
                Amortized -> ConstTerm 1
                
          -- The coefficients of phi-terms are only fixed for types with a
          -- non-trivial potential. For other arguments, and for types whose
          -- potential is identically zero, they are only required to be
          -- non-negative; otherwise the objective is unbounded.
          retZero <- zeroPotential returnType
          carried <- carriedPotTypes returnType
          fromCs <- concat <$> forM (args (fs^.fsFrom)) (\x -> do
            let tx = fnArgType x (fs^.fsFormArgs) tFun
            argZero <- zeroPotential tx
            return $ if tx `elem` carried && not argZero
              then (fs^.fsFrom)!?RTPhi x `eq` pot
              else geZero ((fs^.fsFrom)!?RTPhi x))
          let toCs = concat [case t of
                               i@(RTPhi _) | retZero   -> geZero ((fs^.fsTo)!i)
                                           | otherwise -> (fs^.fsTo)!i `eq` pot
                               i -> zero ((fs^.fsTo)!i)
                            | t <- S.toList $ terms (fs^.fsTo)]
          tellSigCs (fromCs ++ toCs)

-- | The types whose potential is carried by values of the given type: the
-- type itself and, for a product whose potential measure is a sum of the
-- potentials of its components with coefficient 1 (e.g. pot (x, t) = pot t),
-- the types of these components. An argument of a carried type must keep its
-- potential, since the result accounts for it with coefficient 1; otherwise
-- potential that is not returned could be spent as cost.
carriedPotTypes :: Type -> ProveMonad [Type]
carriedPotTypes t@(TAp "(,)" _) | isResourceRelevant t = do
  env <- measureEnvForType t
  let (Equations eqs) = emPotentialMeasure env
      comps = unprod t
  return $ case eqs of
    [(ConstPat _ vars, rhs)]
      | length vars == length comps
      , let fieldTypes = M.fromList (zip vars comps)
      , [x | (RTPhi x, RSConst 1) <- M.toList rhs] `sameAs` M.keys rhs
        -> t : [fieldTypes M.! x | RTPhi x <- M.keys rhs]
    _ -> [t]
  where sameAs xs ts = map RTPhi xs == ts
carriedPotTypes t = return [t]

-- | Whether the potential of values of the given type is identically zero,
-- i.e. all equations of its potential measure have a zero right-hand side.
zeroPotential :: Type -> ProveMonad Bool
zeroPotential t
  | not (isResourceRelevant t) = return True
  | otherwise = do
      env <- measureEnvForType t
      let (Equations eqs) = emPotentialMeasure env
      return $ all (all isZero' . M.elems . snd) eqs
  where isZero' (RSConst 0) = True
        isZero' _ = False


assertSigMatchesAnn :: Program Positioned -> ProveMonad ()
assertSigMatchesAnn prog = do
  M.traverseWithKey go (prog^.pSig)
  return ()
        where go :: Id -> FunSig -> ProveMonad ()
              go fn fsig = case fsig^.costSig of
                Just cs -> do
                  fs <- (M.! fn) <$> use sig
                  
                  tellSigCs $ assertEqVarsSubst (args (fs^.fsFrom)) (csArgs cs)  (fs^.fsFrom) (csFrom cs) 
                  tellSigCs $ assertEqVarsSubst [fs^.fsBinder] [csBinder cs]  (fs^.fsTo) (csTo cs) 
                Nothing -> throwError $ ProofErr ("Missing resource annotation for function"
                                                  ++ " '" ++ show fn ++ "'"
                                                  ++ " in check mode.")


obtainSizeTransforms :: [Id] -> Relation -> ProveMonad ()
obtainSizeTransforms scc rel = do
  fsSig <- use sig
  
  mapM_ go $ M.toList (M.restrictKeys fsSig (S.fromList scc))
  
  where go :: (Id, FreeSig) -> ProveMonad ()
        go (fn, fs) = do
          sol <- use solution
          case sol of
            Just sol -> do
              let boundTempl = bindTemplate (fs^.fsFrom) sol
              let transform = sizeTransformFromTempl (fs^.fsFormArgs) boundTempl rel
              sizeSig . at fn .= Just transform
            Nothing -> error "cannot obtain size transforms without a solution."

  

appendDeriv :: Id -> Derivation -> ProveMonad ()
appendDeriv fn newDeriv = 
  fnDerivs . at fn %= \case
    Nothing     -> Just [newDeriv]
    Just derivs -> Just (derivs ++ [newDeriv]) 
