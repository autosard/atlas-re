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
import Data.Set(Set)
import qualified Data.Tree as T
import qualified Data.List as L


import Primitive(Id, traceShowV)
import CostAnalysis.Annotation hiding (sub, sum)
import CostAnalysis.Predicate
import CostAnalysis.Template (FreeTemplate(..),
                              TemplateArray,
                              TemplateOptions)
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
  _potentials :: P.PotFnMap,
  _auxPotentials :: Map Type Potential,
  _auxMode :: Bool,
  _fnConfig :: FnConfig}

makeLenses ''ProofState

data AnalysisMode
  = CheckCoefficients
  | CheckCost
  | ImproveCost
  | Infer 

data ProofEnv = ProofEnv {
  _tactics :: Map Id Tactic,
  _analysisMode :: AnalysisMode,
  _incremental :: Bool,
  _rhsTerms :: Bool}

data ProofErr
  = DerivErr SourceError
  | UnsatErr [Constraint]

makeLenses ''ProofEnv


isCostFree :: JudgementType -> Bool
isCostFree Standard = False
isCostFree _ = True

cfSigIdx :: JudgementType -> Maybe Int
cfSigIdx (Cf n) = Just n
cfSigIdx _ = Nothing

type Solution = (Map Coeff Rational, String)

type ProveMonad a = ExceptT ProofErr (RWST ProofEnv Solution ProofState IO) a

runProof :: ProofEnv -> ProofState -> ProveMonad a -> IO (Either ProofErr a, ProofState, Solution)
runProof env state proof = let rws = runExceptT proof in
  runRWST rws env state



conclude :: Rule
  -> JudgementType
  -> ProveKind
  -> (FreeAnn, FreeAnn, Set Predicate)
  -> FreeAnn
  -> [Constraint]
  -> PositionedExpr
  -> [Derivation]
  -> ProveMonad Derivation
conclude rule judgeType kind ctx ctx' cs e derivs = do
  tellCs cs
  return $ T.Node (ExprRuleApp rule (isCostFree judgeType) kind ctx ctx' cs e) derivs

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

freshAtom :: ProveMonad Constraint
freshAtom = Atom <$> genVarId

potForType :: Type -> ProveMonad Potential
potForType t = do
  aux <- use auxMode
  if aux
  then do
    auxPots <- use auxPotentials
    return $ auxPots M.! t
  else do
    pots <- use potentials
    return $ maybe
      (error $ "No potential function for type '" ++ show t ++ "' defined.")
      fst (pots M.!? t)

annForType :: Type -> Map Type (Potential, FreeTemplate) -> FreeTemplate
annForType t m = snd $ m M.! t

withPotAndId :: Type -> (Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate)
  -> (Text -> Text -> [Id] -> ProveMonad FreeTemplate)
withPotAndId t f label comment args = do
  pot <- potForType t
  id <- genAnnId
  return $ f pot id label comment args

withId :: (Potential -> Int -> Text -> Text -> [Id] -> FreeTemplate)
  -> (Potential -> Text -> Text -> [Id] -> ProveMonad FreeTemplate)
withId f pot label comment args = do
  id <- genAnnId
  return $ f pot id label comment args

emptyTempl :: Text -> Text -> [Id] -> [Id] -> ProveMonad FreeTemplate
emptyTempl label comment args ghosts = do
  id <- genAnnId
  return $ Templ.emptyTempl id label comment args ghosts

emptyAnn :: Map Type ([Id], [Id]) -> Text -> Text -> ProveMonad FreeAnn
emptyAnn args label comment = do
  templs <- mapM (\(t, (vars, ghosts)) -> (t, ) <$> emptyTempl label comment vars ghosts) $ M.toAscList args
  return $ M.fromList templs

emptyAnnFrom :: FreeAnn -> Text -> Text -> ProveMonad FreeAnn
emptyAnnFrom ann label comment = do
  templs <- mapM (\(t, templ) -> (t, ) <$> emptyTempl label comment (Templ.args templ) (Templ.ghosts templ)) (M.assocs ann)
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

enrichWithDefaults :: TemplateOptions -> Text -> Text -> FreeAnn -> ProveMonad FreeAnn
enrichWithDefaults neg label comment ctx = do
  let qs = M.toAscList ctx
  M.fromList <$> mapM (enrichAnnWithDefaults neg label comment) qs

enrichAnnWithDefaults :: TemplateOptions -> Text -> Text -> (Type, FreeTemplate) -> ProveMonad (Type, FreeTemplate)
enrichAnnWithDefaults opts label comment (t, ann) = do
  pot <- potForType t 
  id <- genAnnId
  return (t, P.enrichWithDefaults pot opts id label comment ann)


freshAnn :: Map Type [Id] -> Text -> Text -> TemplateOptions -> ProveMonad FreeAnn
freshAnn args label comment opts = do
  anns <- mapM (\(t, vars) -> (t, ) <$> freshTempl t opts label comment vars) $ M.toAscList args
  return $ M.fromList anns

defaultAnn :: Map Type [Id] -> Text -> Text  -> ProveMonad FreeAnn
defaultAnn args label comment = do
  anns <- mapM (\(t, vars) -> (t, ) <$> defaultTempl t label comment vars) $ M.toAscList args
  return $ M.fromList anns



singleAnn :: Potential -> Type -> Map Type [Id] -> Text -> Text -> ProveMonad FreeAnn
singleAnn pot nonZeroType args label comment = do
  anns <- mapM templForType $ M.toAscList args
  return $ M.fromList anns
  where templForType (t, vars) = do
          templ <- if t == nonZeroType
                   then defaultTemplFor pot label comment vars 
                   else emptyTempl label comment vars []
          return (t, templ)

freshTempl :: Type -> TemplateOptions -> Text -> Text -> [Id] -> ProveMonad FreeTemplate
freshTempl t opts = withPotAndId t (P.templForPot opts)
  
defaultTempl :: Type -> Text -> Text -> [Id] -> ProveMonad FreeTemplate
defaultTempl t = withPotAndId t P.defaultTemplForPot

defaultTemplFor :: Potential -> Text -> Text -> [Id]  -> ProveMonad FreeTemplate
defaultTemplFor = withId P.defaultTemplForPot

emptyArrayFromIdxs :: Id -> [(JudgementType, CoeffIdx)] -> Text -> [Id] -> [Id] -> ProveMonad TemplateArray
emptyArrayFromIdxs x idxs label args ghosts = templArrayFromIdxs x idxs label args ghosts emptyTempl

defineByShift :: FreeAnn -> FreeAnn -> (Term -> Term) -> ProveMonad (FreeAnn, [Constraint])
defineByShift qs_ ps shift = do
  annsWithPot <- mapM (\(t, q) -> do
                          pot <- potForType t 
                          return (t, pot, q, ps M.! t)) $ M.toAscList qs_
  let (qs, css) = unzip $ map eqExceptConst' annsWithPot
  qConsts <- mapM (\(t, q) -> do
                      pot <- potForType t 
                      return (t, oneCoeff pot)) qs
  pConstTerms <- mapM (\(t, p) -> do
                          pot <- potForType t 
                          return $ p Templ.!? oneCoeff pot) $ M.assocs ps 
  let (qs', cs) = extend (M.fromList qs) $ (`shiftSum` pConstTerms)  <$> defMulti qConsts
  return (qs', concat css ++ cs)
  where eqExceptConst' (t, pot, q, p) = let (q', cs) = defineByExceptConst pot q p in
          ((t, q'), cs)
        shiftSum qs ps = sum qs `eq` shift (sum ps)

defineByMinus :: FreeAnn -> FreeAnn -> Term -> ProveMonad (FreeAnn, [Constraint])
defineByMinus qs_ ps t = defineByShift qs_ ps (\s -> sub [s,t])

defineByPlus :: FreeAnn -> FreeAnn -> Term -> ProveMonad (FreeAnn, [Constraint])
defineByPlus qs_ ps t = defineByShift qs_ ps (\s -> sum [s,t])


templArrayFromIdxs :: Id -> [(JudgementType, CoeffIdx)] -> Text -> [Id] -> [Id]
  -> (Text -> Text -> [Id] -> [Id] -> ProveMonad FreeTemplate)
  -> ProveMonad TemplateArray
templArrayFromIdxs x idxs label args ghosts templGen = do
  anns <- mapM annFromIdx idxs
  return $ M.fromList anns
  where annFromIdx (judgeT, idx) = (idx,) <$> do
          auxMode .= case judgeT of
            (Aux _) -> True
            _ -> False
          t <- templGen (label' idx) "" (addArgs idx ++ args) ghosts
          auxMode .= False
          return t
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' idx = Te.concat [label, "_", Te.pack $ show idx]
        addArgs idx = (coeffArgs . mixed) (restrictFacs idx [2,1]) L.\\ args

annCOptimize :: (FreeAnn, FreeAnn) -> FreeAnn -> ProveMonad [Term]
annCOptimize (qs, qes) qs' = concat <$> mapM go (zip3 (M.assocs qs) (M.assocs qes) (M.assocs qs'))
  where go :: ((Type, FreeTemplate), (Type, FreeTemplate), (Type, FreeTemplate)) -> ProveMonad [Term]
        go ((t, q), (_, qe), (_, q')) = do
          pot <- potForType t
          return $ cOptimize pot (q, qe) q'          
