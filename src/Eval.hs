{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}

module Eval where

import qualified Data.Map as M
import Data.Map(Map)

import Ast
import Primitive(Id)
import Control.Monad (msum)
import Control.Monad.Except (Except, liftEither, runExcept, MonadError (throwError))
import Control.Monad.State(StateT, runStateT)
import Control.Monad.Reader (ReaderT (runReaderT), lift, asks)
import Data.Either.Extra (maybeToEither)
import Constants(constEval, toBool)
import Data.Maybe (fromMaybe)
import System.Random
import Data.Random.Sample
import Data.Random.Distribution.Bernoulli (Bernoulli(Bernoulli))
import Lens.Micro.Platform

defaultCost :: Rational
defaultCost = 1

type Env = Map Id Val

type DefMap = Map Id TypedFunDef

data EvalError
  = UnboundIdentifier !Id
  | NonExaustivePatterns !TypedExpr
  deriving Eq

instance Show EvalError where
  show :: EvalError -> String
  show (UnboundIdentifier id) = "Unbound identifier: '" ++ show id ++ "'"

data EvalState = EvalState {
  _rng :: !StdGen,
  _cost :: !Rational}
  deriving Show

makeLenses ''EvalState
                   
type Eval = ReaderT DefMap (StateT EvalState (Except EvalError))

bernoulli :: Rational -> Bernoulli Double Bool
bernoulli p = Bernoulli (fromRational p) 

flipCoin :: Rational -> Eval Bool
flipCoin p = do
  g <- use rng
  let (b, g') = samplePure (bernoulli p) g
  rng .= g'
  return b

find :: Id -> Env -> Eval Val
find id env = do
  let maybeVal = M.lookup id env
  lift $ liftEither (maybeToEither (UnboundIdentifier id) maybeVal)

evalEval :: DefMap -> EvalState -> Eval a -> Either EvalError (Rational, a)
evalEval defs initState eval = runExcept (
  do
    (val, s) <- (`runStateT` initState) . (`runReaderT` defs) $ eval
    return (s ^. cost, val))

evalWithModule :: TypedModule -> TypedExpr -> StdGen -> Val
evalWithModule mod exp rng = case evalEval defs (EvalState rng 0) (evalExpr M.empty exp) of
  Left e -> error $ show e
  Right (cost, val) -> val
  where defs = M.fromList $ map splitDef mod
        splitDef fun@(Fn id _ _) = (id, fun)

matchPatterns :: Val -> [TypedMatchArm] -> Maybe (Env, TypedExpr)
matchPatterns val arms = msum $ map (matchArm val) arms
  where matchArm val (MatchArm pat e) = (,e) <$> match val pat

match :: Val -> TypedPattern -> Maybe Env
match (LitVal _) _ = Nothing
match (ConstVal id1 args) (ConstPat _ id2 vars)
  | id1 == id2 && length args == length vars = Just $ bindPatVars vars args
match val (Alias _ id) = Just $ M.singleton id val
match _ (WildcardPat _) = Just M.empty
match _ _ = Nothing

bindPatVars :: [PatternVar] -> [Val] -> Env
bindPatVars vars vals = foldr go M.empty $ zip vars vals
  where go (var, val) env = case var of
          (Id id) -> M.insert id val env
          WildcardVar -> env

evalExpr :: Env -> TypedExpr -> Eval Val
evalExpr env (Var id) = find id env
evalExpr env (Lit l) = return $ LitVal l
evalExpr env (ConstAnn ann id args) = do
  args' <- mapM (evalExpr env) args
  return $ constEval id args'
evalExpr env (Ite e1 e2 e3) = do
  val1 <- evalExpr env e1
  case val1 of
    (ConstVal "true" []) -> evalExpr env e2
    (ConstVal "false" []) -> evalExpr env e3
    _nonBool -> error "evaluating test in ITE returned non boolean value"    
evalExpr env me@(Match e arms) = do
  val <- evalExpr env e
  case matchPatterns val arms of
    Just (env', e) -> evalExpr (M.union env' env) e
    Nothing -> throwError (NonExaustivePatterns me)
evalExpr env (App id args) = do
  maybeDef <- asks (M.lookup id)
  def <- lift $ liftEither (maybeToEither (UnboundIdentifier id) maybeDef)
  let (Fn _ argVars body) = def
  args' <- mapM (evalExpr env) args
  let bindings = M.fromList $ zip argVars args'
  let env' = M.union bindings env
  evalExpr env' body
evalExpr env (Let id e1 e2) = do
  val1 <- evalExpr env e1
  let env' = M.insert id val1 env
  evalExpr env' e2
evalExpr env (Coin p) = toBool <$> flipCoin p
evalExpr env (Tick c e) = do
  cost += fromMaybe defaultCost c 
  evalExpr env e
