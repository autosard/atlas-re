{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}


module CostAnalysis.ProveMonad
  ( ProveMonad
  , Solution (..)
  , ProofState (..)
  , sig
  , sizeSig
  , tLang
  , sigCs 
  , optiTargets
  , annIdGen 
  , varIdGen 
  , constraints
  , fnDerivs 
  , solution 
  , measureSig
  , ProofEnv (..)
  , tactics
  , analysisMode
  , incremental
  , costModes 
  , inferPotential
  , ProofErr (..)
  , AnalysisMode (..)
  , OptBound (..)
  , Derivation (..)
  , freshVar
  , errorFrom
  , conclude
  , defineByShift
  , isCostFree
  , freshTempl
  , assertEqSubst
  , freshFrom
  , freshTemplExtend
  , concludeArm
  , defEqSubst
  , measureEnvForType
  , tellSigCs
  , sizeTransformable
  , enrichMeasureSig
  , resetAnalysis
  , potentials
  , runProof
  , ResourceContext
  , addVarConstraints
  , axioms
  ) where

import Prelude hiding (sum)
import Control.Monad.RWS
import Control.Monad.Except
import Lens.Micro.Platform
import Data.Map(Map)
import qualified Data.Map as M
import Data.Tree(Tree)
import qualified Data.Set as S
import qualified Data.Tree as T
import qualified Data.Text as Text


import Syntax (Id, Positioned)
import CostAnalysis.Template hiding (assertEqSubst)
import qualified CostAnalysis.Template as Templ
import CostAnalysis.Rules
import CostAnalysis.Tactic
import SourceError
import CostAnalysis.Constraint
import Syntax.Expression
import Syntax.Pattern
import Syntax.Types.Type
import Syntax.Types.Scheme (Scheme (Forall), findByType, tFunResult)
import Syntax.ResourceExpression.Axioms (AxiomSpec)
import Syntax.Program hiding (AnalysisMode)
import Syntax.Annotation
import CostAnalysis.Coeff
import Syntax.Measure (SizeTransform,
                       Measure(..),
                       MeasureEnv(..),
                       MeasureAlgebra(..),
                       ConstPat(..),
                       sizeGeOne)
import CostAnalysis.TemplateLanguage
import Syntax.ResourceExpression ( ResourceTerm(..), isPotential, ResourceExpr, RScalar (..) )
import Data.Maybe (isJust)
import Control.Monad (forM)
import Control.Monad.Extra (whenM, ifM, mapMaybeM)
import qualified Syntax.FreeModule as FM
import Syntax.ResourceExpression.Inequality (ResourceIneq, sizeGeOneCs)
import Text.Show.Pretty (ppShow)
import Primitive (dbg)


type Derivation = Tree RuleApp

data ProofState = ProofState {
  _sig :: Map Id FreeSig,
  _sizeSig :: Map Id SizeTransform,
  _tLang :: TemplateLanguage,
  _sigCs :: [Formula],
  _optiTargets :: [ArithExpr],
  _annIdGen :: Int,
  _varIdGen :: Int,
  _constraints :: [Formula],
  _fnDerivs :: Map Id [Derivation],
  _solution :: Maybe (Map Coeff Rational),
  _measureSig :: Map Scheme EnrichedMeasureEnv
  }

makeLenses ''ProofState

data AnalysisMode
  = Check
  | Infer
  deriving Eq


data ProofEnv = ProofEnv {
  _tactics :: Map Id Tactic,
  _analysisMode :: AnalysisMode,
  _incremental :: Bool,
  _costModes :: Map Id CostMode,
  _inferPotential :: Bool,
  _axioms :: [AxiomSpec]
  }

makeLenses ''ProofEnv

data ProofErr
  = DerivErr (SourceError String)
  | UnsatErr [Formula]
  | MissingMeasure Type Measure
  | ProofErr String

type ResourceContext = [ResourceIneq]  

enrichMeasureSig :: Program a -> ProveMonad (Map Scheme EnrichedMeasureEnv)
enrichMeasureSig prog = M.traverseWithKey go (prog^.pMeasureSig)
  where go :: Scheme -> MeasureEnv -> ProveMonad EnrichedMeasureEnv
        go t mEnv = do
          potMeasure <- ifM (view inferPotential) 
            (genPotMeasure (prog ^. pDataEnv) t genFreePotExpr)
            (case potentialMeasure mEnv of
               Just pm -> return pm
               Nothing -> genPotMeasure (prog ^. pDataEnv) t genZeroPotExpr)
                  
          return $ EnrichedMeasureEnv {
            emSizeMeasure = sizeMeasure mEnv
            , emPotentialMeasure = potMeasure
            }
          
potentials :: Map Scheme EnrichedMeasureEnv -> Map Scheme [(ConstPat, ResourceExpr)]
potentials = M.map go
  where go :: EnrichedMeasureEnv -> [(ConstPat, ResourceExpr)]
        go env = let (Equations eqs) = emPotentialMeasure env in eqs

genPotMeasure :: DataEnv
  -> Scheme
  -> (Id -> [(Id, Type)] -> ProveMonad (ConstPat, ResourceExpr))
  -> ProveMonad (MeasureAlgebra Potential)
genPotMeasure env (Forall _ (TAp tName _)) genRhs = do
  let ctors = diCtors $ env M.! tName
  
  let ctorInputs = [(cName, args')
                   | CtorInfo cName cType <- ctors
                   , let (Forall _ t) = cType
                         args' = [(Text.pack $ "_pArg" ++ show i, t)
                                 | (t, i) <- zip (funTArgs t) [1..]
                                 ]
                   ]
  eqs <- forM ctorInputs (uncurry genRhs)
  return $ Equations eqs

genZeroPotExpr :: Id -> [(Id, Type)] -> ProveMonad (ConstPat, ResourceExpr)
genZeroPotExpr cName args = do 
  let patArgs = map fst args
  let rhs = FM.empty
  return (ConstPat cName patArgs, rhs)
  

genFreePotExpr :: Id -> [(Id, Type)] -> ProveMonad (ConstPat, ResourceExpr)
genFreePotExpr cName args = do
  let templArgs = map fst $ filter (\(_,t) -> isResourceRelevant t) args
  let patArgs = map fst args

  templ <- freshTempl templArgs
      
  whenM ((== Infer) <$> view analysisMode)
    (do
        abs <- sequence [coeffAbs (templ!t) | t <- S.toList (terms templ)]
        optiTargets %= (sum abs :)
    )
        
  let rhs = FM.fromList' $
            [(t, RSCoeff (templ^.ftId) t)
            | t <- S.toList $ terms templ
            , not (isPotential t)]
            ++
            [(t, 1) 
            | t <- S.toList $ terms templ
            , isPotential t]
  return (ConstPat cName patArgs, rhs)

  

coeffAbs :: ArithExpr -> ProveMonad ArithExpr
coeffAbs q = do
  abs <- freshVar
  tellCs $ geZero abs
           ++ ge abs q
           ++ ge abs (minus q)
  return abs
  
  

isCostFree :: JudgementType -> Bool
isCostFree Standard = False
isCostFree _ = True

newtype OptBound = OptBound String
  deriving Show

instance Semigroup OptBound where
  (<>) (OptBound "") b2 = b2
  (<>) b1 (OptBound "") = b1
  (<>) (OptBound b1) (OptBound b2) = OptBound $ b1 ++ ", " ++ b2
  
instance Monoid OptBound where
  mempty = OptBound ""


type Solution = (Map Coeff Rational, OptBound)

type ProveMonad a = ExceptT ProofErr (RWST ProofEnv Solution ProofState IO) a

runProof :: ProofEnv -> ProofState -> ProveMonad a -> IO (Either ProofErr a, ProofState, Solution)
runProof env state proof = let rws = runExceptT proof in
  runRWST rws env state

conclude :: Rule
  -> JudgementType
  -> FreeTemplate
  -> FreeTemplate
  -> [Formula]
  -> Expr Positioned
  -> [Derivation]
  -> ProveMonad Derivation
conclude rule jt q q' cs e derivs = do
    tellCs cs
    return $ T.Node (ExprRuleApp rule (RuleAppInfo jt q q' cs e)) derivs

concludeArm :: Pattern Positioned
  -> JudgementType
  -> FreeTemplate
  -> FreeTemplate
  -> [Formula]
  -> Expr Positioned
  -> [Derivation]
  -> ProveMonad Derivation
concludeArm pat jt q q' cs e derivs = do
  tellCs cs
  return $ T.Node (MatchArmApp pat (RuleAppInfo jt q q' cs e)) derivs

tellCs :: [Formula] -> ProveMonad ()
tellCs cs = constraints %= (++cs)

tellSigCs :: [Formula] -> ProveMonad ()
tellSigCs cs = sigCs %= (++cs)

errorFrom :: (HasAnnotation b Positioned) => b Positioned -> String -> ProveMonad a
errorFrom e msg = throwError $ DerivErr $ SourceError loc msg
  where loc = case (peSrc . getAnn) e of
          (Loc pos) -> pos
          (DerivedFrom pos) -> pos

resetAnalysis :: ProveMonad ()
resetAnalysis = do
  solution .= Nothing
  sig .= M.empty
  sigCs .= []
  optiTargets .= []
  constraints .= []

genAnnIds :: Int -> ProveMonad [Int]
genAnnIds n = do
  g <- use annIdGen
  annIdGen .= g+n
  return [g..(g+n-1)]

genAnnId :: ProveMonad Int
genAnnId = do
  g <- use annIdGen
  annIdGen .= g+1
  return g

genVarId :: ProveMonad Int
genVarId = do
  g <- use varIdGen
  varIdGen .= g+1
  return g
 
freshVar :: ProveMonad ArithExpr
freshVar = VarTerm <$> genVarId

freshAtom :: ProveMonad Formula
freshAtom = Atom <$> genVarId

freshEmptyTempl :: ProveMonad FreeTemplate
freshEmptyTempl = do
  i <- genAnnId
  return $ FreeTemplate {
    _ftId = i
    , _ftTerms = S.empty
    }

freshFrom :: FreeTemplate -> ProveMonad FreeTemplate
freshFrom src = do
  i <- genAnnId
  return $ Templ.defineFrom i src
    
freshTempl :: [Id] -> ProveMonad FreeTemplate
freshTempl args = do
  i <- genAnnId
  tl <- use tLang
  return $ FreeTemplate {
    _ftId = i
    , _ftTerms = tl args
    }

freshTemplExtend :: FreeTemplate -> ProveMonad FreeTemplate
freshTemplExtend q = do
  i <- genAnnId
  tl <- use tLang
  return $ FreeTemplate {
    _ftId = i
    , _ftTerms = tl (args q) `S.union` terms q
  }

measureEnvForType :: Type -> ProveMonad EnrichedMeasureEnv
measureEnvForType t = do
  mSig <- use measureSig
  case findByType t mSig of
    Just env -> return env
    Nothing -> throwError $ MissingMeasure t Size

addVarConstraints :: [(Id, Type)] -> ResourceContext -> ProveMonad ResourceContext
addVarConstraints xs rctx = do
  rctxs <- mapMaybeM go xs
  return $ rctx ++ concat rctxs
  where go (x, t) =
          if isResourceRelevant t then do
            env <- measureEnvForType t
            return $ Just [sizeGeOneCs x | sizeGeOne (emSizeMeasure env)]
          else return Nothing

defEqSubst :: (Id, SubstValue) -> FreeTemplate -> ProveMonad (FreeTemplate, [Formula])
defEqSubst subst q = do
  p <- freshEmptyTempl
  let (tgtTerms, cs) = Templ.assertEqSubst False subst q p
  return (p & ftTerms .~ tgtTerms, cs)

assertEqSubst :: (Id, SubstValue) -> FreeTemplate -> FreeTemplate  -> ProveMonad [Formula]
assertEqSubst subst q p = do
  let (tgtTerms, cs) = Templ.assertEqSubst True subst q p
  let leftOverTerms = (p^.ftTerms)  S.\\ tgtTerms
  return $ cs ++ concatMap (zero . (p!?)) leftOverTerms

sizeTransformable :: Program Positioned -> Id -> ProveMonad Bool
sizeTransformable prog fn = do
  let tResult = tFunResult $ ((prog^.pSig) M.! fn)^.typeSig
  mSig <- use measureSig
  return $ isJust (findByType tResult mSig)

defineByShift :: (ArithExpr -> ArithExpr) -> FreeTemplate -> ProveMonad (FreeTemplate , [Formula])
defineByShift shift q = do
  p <- freshFrom q
  return (p, assertEqExceptTerm RTId shift p q)  
