{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
module CostAnalysis.ProveMonad where

import Control.Monad.RWS
import Control.Monad.Except
import Lens.Micro.Platform
import Data.Map(Map)

import Primitive(Id)
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential
import CostAnalysis.Tactic
import SourceError
import CostAnalysis.Constraint

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

genAnnIdPair :: ProveMonad (Int, Int)
genAnnIdPair = do
  g <- use annIdGen
  annIdGen .= g+2
  return (g, g+1)

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
freshVar = Var <$> genVarId
