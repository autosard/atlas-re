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
import CostAnalysis.RsrcAnn hiding (fromAnn)
import CostAnalysis.Potential hiding (rsrcAnn, emptyAnn, defaultAnn)
import CostAnalysis.Rules
import qualified CostAnalysis.Potential as P
import qualified CostAnalysis.RsrcAnn as R
import CostAnalysis.Tactic
import SourceError
import CostAnalysis.Constraint
import Typing.Type
import Ast
import CostAnalysis.Coeff
import Data.List(intercalate)
import Data.Foldable (foldrM)
import Data.Maybe (isJust)

type Derivation = Tree RuleApp



data ProofState = ProofState {
  _sig :: RsrcSignature,
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



conclude :: Rule -> Maybe Int -> AnnCtx -> AnnCtx -> [Constraint] -> PositionedExpr -> [Derivation] -> ProveMonad Derivation
conclude rule cf q q' cs e derivs = do
  tellCs cs
  return $ T.Node (ExprRuleApp rule (isJust cf) q q' cs e) derivs

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

potForType :: Type -> Map Type (Potential, RsrcAnn) -> Potential
potForType t m = fst $ m M.! t

annForType :: Type -> Map Type (Potential, RsrcAnn) -> RsrcAnn
annForType t m = snd $ m M.! t

withPotAndId :: Type -> (Potential -> Int -> Text -> Text -> [Id] -> RsrcAnn)
  -> (Text -> Text -> [Id] -> ProveMonad RsrcAnn)
withPotAndId t f label comment args = do
  pot <- potForType t <$> use potentials
  id <- genAnnId
  return $ f pot id label comment args

withId :: (Potential -> Int -> Text -> Text -> [Id] -> RsrcAnn)
  -> (Potential -> Text -> Text -> [Id] -> ProveMonad RsrcAnn)
withId f pot label comment args = do
  id <- genAnnId
  return $ f pot id label comment args

emptyAnn :: Type -> Text -> Text -> [Id] -> ProveMonad RsrcAnn
emptyAnn t = withPotAndId t P.emptyAnn

emptyAnnCtx :: Map Type [Id] -> Text -> Text -> ProveMonad AnnCtx
emptyAnnCtx args label comment = do
  anns <- mapM (\(t, vars) -> (t, ) <$> emptyAnn t label comment vars) $ M.toAscList args
  return $ M.fromList anns

fromAnn :: Text -> Text -> RsrcAnn -> ProveMonad RsrcAnn
fromAnn label comment ann = do
  id <- genAnnId
  return $ R.fromAnn id label comment ann

fromCtx :: Text -> Text -> AnnCtx -> ProveMonad AnnCtx
fromCtx label comment ctx = M.fromList <$> mapM go (M.toList ctx)
  where go (t, ann) = do
          ann' <- fromAnn label comment ann
          return (t, ann')


enrichWithDefaults :: Bool -> Text -> Text -> AnnCtx -> ProveMonad AnnCtx
enrichWithDefaults neg label comment ctx = do
  let qs = M.toAscList ctx
  M.fromList <$> mapM (enrichAnnWithDefaults neg label comment) qs

enrichAnnWithDefaults :: Bool -> Text -> Text -> (Type, RsrcAnn) -> ProveMonad (Type, RsrcAnn)
enrichAnnWithDefaults neg label comment (t, ann) = do
  pot <- potForType t <$> use potentials
  id <- genAnnId
  return (t, P.enrichWithDefaults pot neg id label comment ann)

defaultAnnCtx :: Map Type [Id] -> Text -> Text -> ProveMonad AnnCtx
defaultAnnCtx args label comment = do
  anns <- mapM (\(t, vars) -> (t, ) <$> defaultAnn t label comment vars) $ M.toAscList args
  return $ M.fromList anns
  
defaultAnn :: Type -> Text -> Text -> [Id] -> ProveMonad RsrcAnn
defaultAnn t = withPotAndId t P.defaultAnn

defaultAnn' :: Potential -> Text -> Text -> [Id] -> ProveMonad RsrcAnn
defaultAnn' = withId P.defaultAnn

defaultNegAnn :: Type -> Text -> Text -> [Id] -> ProveMonad RsrcAnn
defaultNegAnn t = withPotAndId t P.defaultNegAnn

annArrayFromIdxs :: Type -> [CoeffIdx] -> Text -> [Id] -> ProveMonad AnnArray
annArrayFromIdxs t idxs label args = do
  anns <- mapM annFromIdx idxs
  return $ M.fromList anns
  where annFromIdx idx = (idx,) <$> emptyAnn t (label' idx) "" args
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' idx = Te.concat [label, "_", Te.pack $ show idx]  

ctxCLetBindingBase :: AnnCtx -> AnnCtx -> ProveMonad (AnnCtx, [Constraint])
ctxCLetBindingBase qs ps_ = foldrM go (M.empty, []) (M.keys qs)
  where go :: Type -> (AnnCtx, [Constraint]) -> ProveMonad (AnnCtx, [Constraint])
        go t (ps, css) = do
          pot <- potForType t <$> use potentials
          let (p', cs) = cLetBindingBase pot (qs M.! t) (ps_ M.! t)
          return (M.insert t p' ps, css ++ cs)

ctxCLetBodyBase :: AnnCtx -> AnnCtx -> AnnCtx -> ProveMonad (AnnCtx, [Constraint])
ctxCLetBodyBase qs rs_ ps' = foldrM go (M.empty, []) (M.keys qs)
  where go :: Type -> (AnnCtx, [Constraint]) -> ProveMonad (AnnCtx, [Constraint])
        go t (ps, css) = do
          pot <- potForType t <$> use potentials
          let (p', cs) = cLetBodyBase pot (qs M.! t) (rs_ M.! t) (ps' M.! t)
          return (M.insert t p' ps, css ++ cs)

ctxDefByConstShift :: AnnCtx -> AnnCtx -> (Term -> Term) -> ProveMonad (AnnCtx, [Constraint])
ctxDefByConstShift qs_ ps shift = do
  pots <- use potentials
  let annsWithPot = map (\(t, q) -> (t, potForType t pots, q, ps M.! t)) $ M.toAscList qs_
  let (qs, css) = unzip $ map eqExceptConst' annsWithPot
  let qConsts = map (\(t, q) -> (t, oneCoeff (potForType t pots))) qs
  let pConstTerms = M.elems $ M.mapWithKey (\t p -> p!?oneCoeff (potForType t pots)) ps
  let (qs', cs) = extendCtx (M.fromList qs) $ (`shiftSum` pConstTerms)  <$> defMulti qConsts
  return (qs', concat css ++ cs)
  where eqExceptConst' (t, pot, q, p) = let (q', cs) = eqExceptConst pot q p in
          ((t, q'), cs)
        shiftSum qs ps = sum qs `eq` shift (sum ps)

ctxDefByPlus :: AnnCtx -> AnnCtx -> Term -> ProveMonad (AnnCtx, [Constraint])
ctxDefByPlus qs_ ps t = ctxDefByConstShift qs_ ps (\s -> sum [s,t])
        
ctxDefByMinus :: AnnCtx -> AnnCtx -> Term -> ProveMonad (AnnCtx, [Constraint])
ctxDefByMinus qs_ ps t = ctxDefByConstShift qs_ ps (\s -> sub [s,t])

ctxCOptimize :: AnnCtx -> AnnCtx -> ProveMonad Term
ctxCOptimize qs qs' = sum <$> mapM go (zip (M.assocs qs) (M.assocs qs'))
  where go :: ((Type, RsrcAnn), (Type, RsrcAnn)) -> ProveMonad Term
        go ((t, q), (_, q')) = do
          pot <- potForType t <$> use potentials
          return $ cOptimize pot q q'
