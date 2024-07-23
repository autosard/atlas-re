{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
module CostAnalysis.ProveMonad where

import Control.Monad.RWS
import Control.Monad.Except
import Lens.Micro.Platform
import Data.Map(Map)
import Data.Text(Text)

import Primitive(Id)
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential hiding (rsrcAnn)
import qualified CostAnalysis.Potential as P(rsrcAnn)
import CostAnalysis.Tactic
import SourceError
import CostAnalysis.Constraint
import Typing.Type

data ProofState = ProofState {
  _sig :: RsrcSignature,
  _annIdGen :: Int,
  _varIdGen :: Int
  }
  deriving (Show)

makeLenses ''ProofState

data ProofEnv = ProofEnv {
  _potential :: Potential,
  _tactics :: Map Id Tactic
  }

makeLenses ''ProofEnv

type ProveMonad a = ExceptT SourceError (RWS ProofEnv [Constraint] ProofState) a

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

freshVar :: ProveMonad Var
freshVar = Var False <$> genVarId

freshPosVar :: ProveMonad Var
freshPosVar = Var True <$> genVarId

rsrcAnn :: Text -> [(Id, Type)] -> ProveMonad RsrcAnn
rsrcAnn label vars = do
  pot <- view potential
  id <- genAnnId
  let (ann, cs) = P.rsrcAnn pot id label vars
  tell cs
  return ann

