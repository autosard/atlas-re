{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module CostAnalysis.Analysis where

import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T
import Lens.Micro.Platform

import Primitive(Id)
import Ast
import CostAnalysis.Solving (solve)
import CostAnalysis.ProveMonad
import CostAnalysis.Constraint
import SourceError
import CostAnalysis.Rules
import Control.Monad.Except (MonadError(throwError))
import CostAnalysis.Deriv
import CostAnalysis.Coeff
import Typing.Type
import CostAnalysis.RsrcAnn (RsrcAnn, RsrcSignature)
import Data.List.Extra (allSame)

analyzeModule :: ProofEnv -> PositionedModule
  -> IO (Either SourceError (Derivation, RsrcSignature, Either [Constraint] Solution))
analyzeModule env mod = do
  let state = ProofState M.empty [] 0 0 [] [] M.empty
  case argForRHS mod of
    Left err -> return $ Left err
    Right arg -> do
      (result, state', solution) <- runProof env state (analyzeModule' mod)
      let deriv = T.Node (ProgRuleApp mod) (state'^.fnDerivs)
      case result of
        Left (DerivErr srcErr) -> return (Left srcErr)
        Left (UnsatErr core) -> return (Right (deriv, state'^.sig, Left core))
        Right _ -> return (Right (deriv, state'^.sig, Right solution))

analyzeModule' :: PositionedModule -> ProveMonad ()
analyzeModule' mod = 
  case argForRHS mod of
    Left err -> throwError $ DerivErr err
    Right arg -> do
      -- unique right hand side for the whole module
      rhs <- defaultAnn "Q'" "fn" [arg]
      mapM_ (analyzeBindingGroup mod rhs) (mutRecGroups mod)
    
  
analyzeBindingGroup :: PositionedModule -> RsrcAnn -> [Id]  -> ProveMonad ()
analyzeBindingGroup mod rhs fns = do
  derivs <- mapM (\fn -> proveFun rhs $ defs mod M.! fn) fns
  fnDerivs %= (++derivs)
  solution <- solve fns
  addSigCs fns solution
  tell solution
  
addSigCs :: [Id] -> Solution -> ProveMonad ()
addSigCs fns solution = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  let cs = concatMap go (getCoeffs sig')
  sigCs %= (++cs)
  where go coeff = eq (CoeffTerm coeff) (ConstTerm (solution M.! coeff))
  
argForRHS :: Module Positioned -> Either SourceError (Id, Type)
argForRHS mod = if allSame args then Right $ head args else
  Left $ SourceError (tfLoc $ funAnn (head $ fns mod))
  "Cost analysis requries all involved functions to have the same return type to guarantee consistent a consistent potential function."
  where args = map go (concat $ mutRecGroups mod)
        go fn = snd . ctxFromFn $ defs mod M.! fn
