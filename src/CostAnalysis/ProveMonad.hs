{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.ProveMonad where

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
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential hiding (rsrcAnn, emptyAnn)
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

type Derivation = Tree RuleApp

data ProofState = ProofState {
  _sig :: RsrcSignature,
  _sigCs :: [Constraint],
  _optiTargets :: [Term],
  _annIdGen :: Int,
  _varIdGen :: Int,
  _constraints :: [Constraint],
  _fnDerivs :: [Derivation],
  _solution :: Map Coeff Rational
  }

makeLenses ''ProofState

data AnalysisMode
  = CheckCoefficients
  | CheckCost
  | ImproveCost
  | Infer 

data ProofEnv = ProofEnv {
  _potential :: Potential,
  _tactics :: Map Id Tactic,
  _analysisMode :: AnalysisMode,
  _incremental :: Bool
  }

data ProofErr
  = DerivErr SourceError
  | UnsatErr [Constraint]

makeLenses ''ProofEnv

type Solution = Map Coeff Rational

type ProveMonad a = ExceptT ProofErr (RWST ProofEnv Solution ProofState IO) a

runProof :: ProofEnv -> ProofState -> ProveMonad a -> IO (Either ProofErr a, ProofState, Solution)
runProof env state proof = let rws = runExceptT proof in
  runRWST rws env state



conclude :: Rule -> Bool -> RsrcAnn -> RsrcAnn -> [Constraint] -> PositionedExpr -> [Derivation] -> ProveMonad Derivation
conclude rule cf q q' cs e derivs = do
  tellCs cs
  return $ T.Node (ExprRuleApp rule cf q q' cs e) derivs

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

withPotAndId :: (Potential -> Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn)
  -> (Text -> Text -> [(Id, Type)] -> ProveMonad RsrcAnn)
withPotAndId f label comment args = do
  pot <- view potential
  id <- genAnnId
  return $ f pot id label comment args

emptyAnn :: Text -> Text -> [(Id, Type)] -> ProveMonad RsrcAnn
emptyAnn = withPotAndId P.emptyAnn

fromAnn :: Text -> Text -> RsrcAnn -> ProveMonad RsrcAnn
fromAnn label comment ann = do
  id <- genAnnId
  return $ R.fromAnn id label comment ann

enrichWithDefaults :: Bool -> Text -> Text -> RsrcAnn -> ProveMonad RsrcAnn
enrichWithDefaults neg label comment ann = do
  pot <- view potential
  id <- genAnnId
  return $ P.enrichWithDefaults pot neg id label comment ann
  
defaultAnn :: Text -> Text -> [(Id, Type)] -> ProveMonad RsrcAnn
defaultAnn = withPotAndId P.defaultAnn

defaultNegAnn :: Text -> Text -> [(Id, Type)] -> ProveMonad RsrcAnn
defaultNegAnn = withPotAndId P.defaultNegAnn



annArrayFromIdxs :: [CoeffIdx] -> Text -> [(Id, Type)] -> ProveMonad AnnArray
annArrayFromIdxs idxs label args = do
  anns <- mapM annFromIdx idxs
  return $ M.fromList anns
  where annFromIdx idx = (idx,) <$> emptyAnn (label' idx) "" args
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' idx = Te.concat [label, "_", Te.pack $ show idx]
  
