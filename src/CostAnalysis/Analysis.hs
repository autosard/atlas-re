{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

module CostAnalysis.Analysis where

import Prelude hiding (sum, (!?))
import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Micro.Platform

import System.Exit (die)

import Primitive(Id, prettyPrint)
import Syntax.Ast
import CostAnalysis.Solving (solve)
import CostAnalysis.Constraint hiding (and, sum)
import SourceError
-- import CostAnalysis.Rules
import Control.Monad.Except (MonadError (throwError))
import CostAnalysis.Deriv
import Typing.Type
import Typing.Scheme (tFunArgs, Scheme(..))
import Syntax.Measure (SizeTransform, ConstPat)
-- import CostAnalysis.Potential(PotFnMap, Potential (cExternal), auxSigs)
-- import CostAnalysis.Potential.Kind (fromKind)

import CostAnalysis.Template
import CostAnalysis.TemplateLanguage
import CostAnalysis.ProveMonad
import CostAnalysis.Rules (JudgementType (..))
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Order (computeStratifiedCosts)
import CostAnalysis.Constraint (sum)
import CostAnalysis.Coeff (Coeff(Coeff))
import Control.Monad.Extra (whenM, filterM)


data AnalysisResult = AnalysisResult {
  _arDerivs :: Map Id [Derivation]
  , _arSig :: Map Id FreeSig
  , _arSigCs :: [Formula]
  , _arSizeSig :: Map Id SizeTransform
  , _arResult :: Either [Formula] Solution
  , _arPotSig :: Map Scheme [(ConstPat, FreeTemplate)]
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
  tLang .= fromConfig (templateConfig (prog^.pConfig))
  initMeasureSig prog
  potOptiTgts <- use optiTargets
  
  analyzeSize prog

  resetAnalysis
  optiTargets .= potOptiTgts
  analyzeCost prog

analyzeSize :: Program Positioned -> ProveMonad ()
analyzeSize prog = do
  tLang .= sizeTLang
  initSizeSig prog
  constrainSigForSize prog
  optimizeSig prog
  analyzeProg Cf prog

  obtainSizeTransforms

analyzeCost :: Program Positioned -> ProveMonad ()
analyzeCost prog = do
  tLang .= fromConfig (templateConfig (prog^.pConfig))
  initCostSig prog
  constrainSig prog
  
  analyzeProg Standard prog

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
    analyzeBindingGroup mode prog (concat $ prog^.pMutRecGroups)

analyzeBindingGroup :: JudgementType -> Program Positioned -> [Id]  -> ProveMonad ()
analyzeBindingGroup mode prog fns = do
  mapM_ go fns
  sol <- solve fns
  tell sol
  solution .= Just (fst sol)
  where go :: Id -> ProveMonad ()
        go fn = whenM (M.member fn <$> use sig) $ do
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
            terms' = S.filter (not . isZero) (templ^.ftTerms)
            termsWithCost = computeStratifiedCosts [] terms'
            costTerm = sum [prod2 (ConstTerm (fromIntegral (c*c))) (CoeffTerm (Coeff (templ^.ftId) t))
                           | (t, c) <- termsWithCost]
        

constrainSig :: Program Positioned -> ProveMonad ()
constrainSig prog = do
  mode <- view analysisMode
  case mode of
    Check -> assertSigMatchesAnn prog
    Infer -> do
      assertPotential
      optimizeSig prog

assertPotential :: ProveMonad ()
assertPotential = mapM_ go . M.toList =<< use sig
  where go :: (Id, FreeSig) -> ProveMonad ()
        go (fn, fs) = do
          costMode <- M.findWithDefault Amortized fn <$> view costModes

          let pot = case costMode of
                WorstCase -> ConstTerm 0
                Amortized -> ConstTerm 1
                
          let fromCs = concat [(fs^.fsFrom)!?RTPhi x `eq` pot | x <- args (fs^.fsFrom)]
          let toCs = concat [case t of
                               i@(RTPhi _) -> (fs^.fsTo)!i `eq` pot
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
