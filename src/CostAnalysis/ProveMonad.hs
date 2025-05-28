{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.ProveMonad where

import Prelude hiding (sum)
import Control.Monad.RWS
import Control.Monad.Except
import Lens.Micro.Platform
import Data.Map(Map)
import qualified Data.Map as M
import Data.Text(Text)
import qualified Data.Text as Te
import Data.Tree(Tree)
import qualified Data.Set as S
import qualified Data.Tree as T


import Primitive(Id)
import CostAnalysis.Annotation hiding (sub, sum)
import CostAnalysis.Template (FreeTemplate(..),
                              TemplateArray)
import CostAnalysis.Potential hiding (rsrcAnn, emptyAnn, defaultTempl)
import CostAnalysis.Rules
import qualified CostAnalysis.Potential as P
import qualified CostAnalysis.Template as Templ
--import qualified CostAnalysis.Template
import CostAnalysis.Tactic
import SourceError
import CostAnalysis.Constraint
import Typing.Type
import Ast
import CostAnalysis.Coeff
import Data.List(intercalate)
import Data.Maybe (isJust)

type Derivation = Tree RuleApp



data ProofState = ProofState {
  _sig :: FreeSignature,
  _sigCs :: [Constraint],
  _optiTargets :: [Term],
  _annIdGen :: Int,
  _varIdGen :: Int,
  _constraints :: [Constraint],
  _fnDerivs :: [Derivation],
  _solution :: Map Coeff Rational,
  _potentials :: P.PotFnMap}

makeLenses ''ProofState

data AnalysisMode
  = CheckCoefficients
  | CheckCost
  | ImproveCost
  | Infer 

data ProofEnv = ProofEnv {
  _tactics :: Map Id Tactic,
  _analysisMode :: AnalysisMode,
  _incremental :: Bool}

data ProofErr
  = DerivErr SourceError
  | UnsatErr [Constraint]

makeLenses ''ProofEnv

type Solution = Map Coeff Rational

type ProveMonad a = ExceptT ProofErr (RWST ProofEnv Solution ProofState IO) a

runProof :: ProofEnv -> ProofState -> ProveMonad a -> IO (Either ProofErr a, ProofState, Solution)
runProof env state proof = let rws = runExceptT proof in
  runRWST rws env state



conclude :: Rule -> Maybe Int -> (FreeAnn, FreeAnn) -> FreeAnn -> [Constraint] -> PositionedExpr -> [Derivation] -> ProveMonad Derivation
conclude rule cf (q, qe) q' cs e derivs = do
  tellCs cs
  return $ T.Node (ExprRuleApp rule (isJust cf) (q, qe) q' cs e) derivs

tellCs :: [Constraint] -> ProveMonad ()
tellCs cs = constraints %= (++cs)

tellSigCs :: [Constraint] -> ProveMonad ()
tellSigCs cs = sigCs %= (++cs)

errorFrom :: Syntax Positioned -> String -> ProveMonad a
errorFrom e msg = throwError $ DerivErr $ SourceError loc msg
  where loc = case (peSrc . getAnn) e of
          (Loc pos) -> pos
          (DerivedFrom pos) -> pos

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

freshVar :: ProveMonad Term
freshVar = VarTerm <$> genVarId

potForType :: Type -> Map Type (Potential, FreeTemplate) -> Potential
potForType t m = maybe
  (error $ "No potential function for type '" ++ show t ++ "' defined.")
  fst (m M.!? t)

annForType :: Type -> Map Type (Potential, FreeTemplate) -> FreeTemplate
annForType t m = snd $ m M.! t

withPotAndId :: Type -> (Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate)
  -> (Text -> Text -> [Id] -> ProveMonad FreeTemplate)
withPotAndId t f label comment args = do
  pot <- potForType t <$> use potentials
  id <- genAnnId
  return $ f pot id label comment args

withId :: (Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate)
  -> (Potential -> Text -> Text -> [Id] -> ProveMonad FreeTemplate)
withId f pot label comment args = do
  id <- genAnnId
  return $ f pot id label comment args

emptyTempl :: Type -> Text -> Text -> [Id] -> ProveMonad FreeTemplate
emptyTempl t = withPotAndId t P.emptyAnn

emptyAnn :: Map Type [Id] -> Text -> Text -> ProveMonad FreeAnn
emptyAnn args label comment = do
  templs <- mapM (\(t, vars) -> (t, ) <$> emptyTempl t label comment vars) $ M.toAscList args
  return $ M.fromList templs

fromTempl :: Text -> Text -> FreeTemplate -> ProveMonad FreeTemplate
fromTempl label comment ann = do
  id <- genAnnId
  return $ Templ.defineFrom id label comment ann

fromAnn :: Text -> Text -> FreeAnn -> ProveMonad FreeAnn
fromAnn label comment ctx = M.fromList <$> mapM go (M.toList ctx)
  where go (t, templ) = do
          templ' <- fromTempl label comment templ
          return (t, templ')

enrichWithDefaults :: Bool -> Text -> Text -> FreeAnn -> ProveMonad FreeAnn
enrichWithDefaults neg label comment ctx = do
  let qs = M.toAscList ctx
  M.fromList <$> mapM (enrichAnnWithDefaults neg label comment) qs

enrichAnnWithDefaults :: Bool -> Text -> Text -> (Type, FreeTemplate) -> ProveMonad (Type, FreeTemplate)
enrichAnnWithDefaults neg label comment (t, ann) = do
  pot <- potForType t <$> use potentials
  id <- genAnnId
  return (t, P.enrichWithDefaults pot neg id label comment ann)

defaultAnn :: Map Type [Id] -> Text -> Text -> ProveMonad FreeAnn
defaultAnn args label comment = do
  anns <- mapM (\(t, vars) -> (t, ) <$> defaultTempl t label comment vars) $ M.toAscList args
  return $ M.fromList anns
  
defaultTempl :: Type -> Text -> Text -> [Id] -> ProveMonad FreeTemplate
defaultTempl t = withPotAndId t P.defaultTempl

defaultTemplFor :: Potential -> Text -> Text -> [Id] -> ProveMonad FreeTemplate
defaultTemplFor = withId P.defaultTempl

defaultNegTempl :: Type -> Text -> Text -> [Id] -> ProveMonad FreeTemplate
defaultNegTempl t = withPotAndId t P.defaultNegTempl

emptyArrayFromIdxs :: Type -> [CoeffIdx] -> Text -> [Id] -> ProveMonad TemplateArray
emptyArrayFromIdxs t idxs label args = templArrayFromIdxs t idxs label args emptyTempl

defaultArrayFromIdxs :: Type -> [CoeffIdx] -> Text -> [Id] -> ProveMonad TemplateArray
defaultArrayFromIdxs t idxs label args = templArrayFromIdxs t idxs label args defaultTempl

defineByShift :: FreeAnn -> FreeAnn -> (Term -> Term) -> ProveMonad (FreeAnn, [Constraint])
defineByShift qs_ ps shift = do
  pots <- use potentials
  let annsWithPot = map (\(t, q) -> (t, potForType t pots, q, ps M.! t)) $ M.toAscList qs_
  let (qs, css) = unzip $ map eqExceptConst' annsWithPot
  let qConsts = map (\(t, q) -> (t, oneCoeff (potForType t pots))) qs
  let pConstTerms = M.elems $ M.mapWithKey (\t p -> p Templ.!? oneCoeff (potForType t pots)) ps
  let (qs', cs) = extend (M.fromList qs) $ (`shiftSum` pConstTerms)  <$> defMulti qConsts
  return (qs', concat css ++ cs)
  where eqExceptConst' (t, pot, q, p) = let (q', cs) = defineByExceptConst pot q p in
          ((t, q'), cs)
        shiftSum qs ps = sum qs `eq` shift (sum ps)

defineByMinus :: FreeAnn -> FreeAnn -> Term -> ProveMonad (FreeAnn, [Constraint])
defineByMinus qs_ ps t = defineByShift qs_ ps (\s -> sub [s,t])

defineByPlus :: FreeAnn -> FreeAnn -> Term -> ProveMonad (FreeAnn, [Constraint])
defineByPlus qs_ ps t = defineByShift qs_ ps (\s -> sum [s,t])


templArrayFromIdxs :: Type -> [CoeffIdx] -> Text -> [Id] ->
  (Type -> Text -> Text -> [Id] -> ProveMonad FreeTemplate) -> ProveMonad TemplateArray
templArrayFromIdxs t idxs label args templGen = do
  anns <- mapM annFromIdx idxs
  return $ M.fromList anns
  where annFromIdx idx = (idx,) <$> templGen t (label' idx) "" args
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' idx = Te.concat [label, "_", Te.pack $ show idx]  

annCOptimize :: FreeAnn -> FreeAnn -> ProveMonad Term
annCOptimize qs qs' = sum <$> mapM go (zip (M.assocs qs) (M.assocs qs'))
  where go :: ((Type, FreeTemplate), (Type, FreeTemplate)) -> ProveMonad Term
        go ((t, q), (_, q')) = do
          pot <- potForType t <$> use potentials
          return $ cOptimize pot q q'          
