{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}

module CostAnalysis.ProveMonad where

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


import Primitive(Id)
import CostAnalysis.Template hiding (assertEqSubst)
import qualified CostAnalysis.Template as Templ
import CostAnalysis.Rules
import CostAnalysis.Tactic
import SourceError
import CostAnalysis.Constraint
import Typing.Type
import Typing.Scheme (Scheme (Forall), findByType, tFunResult)
import Syntax.Ast hiding (AnalysisMode)
import CostAnalysis.Coeff
import Syntax.Measure (SizeTransform,
                       Measure(..),
                       MeasureEnv(..),
                       MeasureAlgebra(..),
                       ConstPat(..))
import CostAnalysis.TemplateLanguage
import Syntax.ResourceExpression ( ResourceTerm(..), isPotential )
import Data.Maybe (isJust, mapMaybe)
import Control.Monad (forM)
import Control.Arrow (Arrow(second))
import Data.List (uncons)
import Control.Monad.Extra (whenM)
import Data.Monoid (Last)


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
  _inferPotential :: Bool
  }

data ProofErr
  = DerivErr (SourceError String)
  | UnsatErr [Formula]
  | MissingMeasure Type Measure
  | ProofErr String

makeLenses ''ProofEnv

enrichMeasureSig :: Program a -> ProveMonad (Map Scheme EnrichedMeasureEnv)
enrichMeasureSig prog = M.traverseWithKey go (prog^.pMeasureSig)
  where go :: Scheme -> MeasureEnv -> ProveMonad EnrichedMeasureEnv
        go t mEnv = do
          potMeasure <- case potentialMeasure mEnv of
                Just pm -> return pm
                Nothing -> genPotMeasure (prog ^. pDataEnv) t
                  
          return $ EnrichedMeasureEnv {
            emSizeMeasure = sizeMeasure mEnv
            , emPotentialMeasure = Just potMeasure
            }
          
potentials :: Map Scheme EnrichedMeasureEnv -> Map Scheme [(ConstPat, FreeTemplate)]
potentials = M.mapMaybe go
  where go env = do
          (Equations eqs) <- emPotentialMeasure env
          return $ map (second toTempl) eqs
        toTempl :: [ResourceTerm] -> FreeTemplate
        toTempl terms = let ts = mapMaybe go terms in
                            case uncons ts of
                              Just ((i, _), _) -> FreeTemplate i (S.fromList (map snd ts))
                              Nothing -> FreeTemplate 0 S.empty
          where go (RTCoeffScale i idx _) = Just (i, idx)
                go _ = Nothing


genPotMeasure :: DataEnv -> Scheme -> ProveMonad (MeasureAlgebra Potential)
genPotMeasure env (Forall _ (TAp tName _)) = do
  let ctors = diCtors $ env M.! tName

  let ctorInputs = [(cName, args')
                   | CtorInfo cName cType <- ctors
                   ,  let (Forall _ t) = cType
                          args' = [(Text.pack $ "_pArg" ++ show i, t)
                                  | (t, i) <- zip (funTArgs t) [1..]
                                  ]
                   ]
                   
  eqs <- forM ctorInputs $ \(cName, args') -> do 
      let templArgs = map fst $ filter (\(_,t) -> isResourceRelevant t) args'
      let patArgs = map fst args'

      templ <- freshTempl templArgs
      
      whenM ((== Infer) <$> view analysisMode)
        (do
            abs <- sequence [coeffAbs (templ!t) | t <- S.toList (terms templ)]
--          let negCoeffs = [minus (templ!t) | t <- S.toList (terms templ)]
            optiTargets %= (sum abs :)
        )
        
      let rhs = [RTCoeffScale (templ^.ftId) t t
              | t <- S.toList $ terms templ
              , not (isPotential t)]
              ++ [RTScale 1 t 
                 | t <- S.toList $ terms templ
                 , isPotential t]
      return (ConstPat cName patArgs, rhs)

  return $ Equations eqs

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

errorFrom :: Syntax Positioned -> String -> ProveMonad a
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

measureEnvForType :: Type -> ProveMonad EnrichedMeasureEnv
measureEnvForType t = do
  mSig <- use measureSig
  case findByType t mSig of
    Just env -> return env
    Nothing -> throwError $ MissingMeasure t Size

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
