{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- | A big-step interpreter that counts the ticks of an evaluation. It works on
-- loaded programs (elaborated, typed and normalised), and on expressions of
-- any stage, so that expressions given on the command line can be evaluated
-- without type checking.
module Eval
  ( Val (..)
  , EvalError (..)
  , EvalResult (..)
  , evalInProgram
  , printVal
  ) where

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Text as T
import Data.Ratio (numerator, denominator)
import Data.Maybe (fromMaybe)
import Control.Monad (msum, zipWithM)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, runState)
import Control.Monad.Reader (ReaderT, runReaderT, asks)
import System.Random (StdGen, uniformR)
import Lens.Micro.Platform

import Syntax (Id, Positioned)
import Syntax.Expression
import Syntax.Pattern
import Syntax.Program

data Val = ConstVal !Id ![Val]
  deriving (Eq, Show)

data EvalError
  = UnboundIdentifier !Id
  | UndefinedFunction !Id
  | NonExhaustivePatterns !String
  | RuntimeError !String
    -- | a call of @error@, e.g. for a raised exception of the RaML source
  | ErrorCall !String
  deriving Eq

instance Show EvalError where
  show (UnboundIdentifier x) = "Unbound identifier '" ++ T.unpack x ++ "'."
  show (UndefinedFunction f) = "Undefined function '" ++ T.unpack f ++ "'."
  show (NonExhaustivePatterns e) = "Non-exhaustive patterns in '" ++ e ++ "'."
  show (RuntimeError msg) = msg
  show (ErrorCall msg) = "error " ++ msg

-- | The cost is also reported for evaluations that end in a call of @error@.
data EvalResult = EvalResult
  { erCost :: !Rational
  , erVal :: !(Either String Val)
  } deriving Show

type Env = Map Id Val

data EvalEnv = EvalEnv
  { _eeDefs :: Map Id (FunDef Positioned)
    -- | position of each constructor in its data type, for comparisons
  , _eeCtorIndex :: Map Id Int
  }

data EvalState = EvalState
  { _rng :: !StdGen
  , _cost :: !Rational
  }

makeLenses ''EvalEnv
makeLenses ''EvalState

type Eval = ReaderT EvalEnv (ExceptT EvalError (State EvalState))

defaultCost :: Rational
defaultCost = 1

-- | Evaluates the expression with the functions of the program. Returns the
-- result, the incurred cost and the updated random generator (used by coins).
evalInProgram :: Program Positioned -> Expr a -> StdGen -> Either EvalError (EvalResult, StdGen)
evalInProgram prog e g =
  case (`runState` EvalState g 0) . runExceptT . (`runReaderT` env) $ evalExpr M.empty e of
    (Right v, s) -> Right (EvalResult (s ^. cost) (Right v), s ^. rng)
    (Left (ErrorCall msg), s) -> Right (EvalResult (s ^. cost) (Left msg), s ^. rng)
    (Left err, _) -> Left err
  where env = EvalEnv (prog ^. pFunDefs) ctorIndex
        ctorIndex = M.fromList
          [ (ciName c, i)
          | info <- M.elems (prog ^. pDataEnv)
          , (i, c) <- zip [0..] (diCtors info) ]

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

natVal :: Int -> Val
natVal 0 = ConstVal "Zero" []
natVal n = ConstVal "Suc" [natVal (n - 1)]

fromNat :: Val -> Maybe Int
fromNat (ConstVal "Zero" []) = Just 0
fromNat (ConstVal "Suc" [n]) = (+ 1) <$> fromNat n
fromNat _ = Nothing

boolVal :: Bool -> Val
boolVal True = ConstVal "True" []
boolVal False = ConstVal "False" []

-- | Prints values in ATLAS syntax, with natural numbers as literals.
printVal :: Val -> String
printVal = go False
  where go _ v | Just n <- fromNat v = show n
        go _ (ConstVal "(,)" [x, y]) = "(" ++ go False x ++ ", " ++ go False y ++ ")"
        go _ (ConstVal c []) = T.unpack c
        go nested (ConstVal c args) = paren nested $ unwords (T.unpack c : map (go True) args)
        paren True s = "(" ++ s ++ ")"
        paren False s = s

-- | Structural order on values: constructors are ordered as in their data
-- declaration (e.g. Zero < Suc), arguments lexicographically.
compareVal :: Map Id Int -> Val -> Val -> Ordering
compareVal idx (ConstVal c1 args1) (ConstVal c2 args2) =
  case compare (rank c1) (rank c2) of
    EQ -> mconcat (zipWith (compareVal idx) args1 args2)
    o -> o
  where rank c = (M.lookup c idx, c)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

lookupVar :: Id -> Env -> Eval Val
lookupVar x env = maybe (throwError (UnboundIdentifier x)) return (M.lookup x env)

flipCoin :: Rational -> Eval Bool
flipCoin p = do
  g <- use rng
  let d = denominator p
      (k, g') = uniformR (0, d - 1) g
  rng .= g'
  return (k < numerator p)

evalExpr :: Env -> Expr a -> Eval Val
evalExpr env (Var x) = lookupVar x env
evalExpr _ (Lit (LNat n)) = return $ natVal n
evalExpr _ (Lit (LString s)) = return $ ConstVal (T.pack (show s)) []
evalExpr _ (Lit l) = throwError $ RuntimeError ("Literal " ++ show l ++ " is not a value.")
evalExpr env (Const c args) = ConstVal c <$> mapM (evalExpr env) args
evalExpr env (Ite e1 e2 e3) = do
  b <- evalExpr env e1
  case b of
    ConstVal "True" [] -> evalExpr env e2
    ConstVal "False" [] -> evalExpr env e3
    v -> throwError $ RuntimeError ("Condition evaluated to the non-boolean " ++ printVal v ++ ".")
evalExpr env e@(Match scrut arms) = do
  v <- evalExpr env scrut
  case msum [ (, body) <$> matchPat v pat | MatchArm pat body <- arms ] of
    Just (binds, body) -> evalExpr (M.union binds env) body
    Nothing -> throwError $ NonExhaustivePatterns (printExprHead' e)
  where printExprHead' = takeWhile (/= '\n') . printExpr (const "") 0
evalExpr env (Let x e1 e2) = do
  v <- evalExpr env e1
  evalExpr (M.insert x v env) e2
evalExpr env (Tick c e) = do
  cost += fromMaybe defaultCost c
  evalExpr env e
evalExpr _ (Coin p) = boolVal <$> flipCoin p
evalExpr env (App "error" args) = do
  vals <- mapM (evalExpr env) args
  throwError $ ErrorCall (unwords (map printVal vals))
evalExpr env (App f args) = do
  vals <- mapM (evalExpr env) args
  case (f, vals) of
    (op, [v1, v2]) | Just cmp <- lookup op comparisons -> do
      idx <- view eeCtorIndex
      return $ boolVal (cmp (compareVal idx v1 v2))
    _ -> do
      def <- asks (M.lookup f . _eeDefs) >>= maybe (throwError (UndefinedFunction f)) return
      let params = def ^. funArgs
      if length params /= length vals
        then throwError $ RuntimeError ("Function '" ++ T.unpack f ++ "' expects "
                                         ++ show (length params) ++ " arguments, got "
                                         ++ show (length vals) ++ ".")
        else evalExpr (M.fromList (zip params vals)) (def ^. funBody)
  where comparisons =
          [ ("<", (== LT)), ("<=", (/= GT)), (">", (== GT))
          , (">=", (/= LT)), ("==", (== EQ)) ]
evalExpr _ _ = throwError $ RuntimeError "Unsupported expression."

matchPat :: Val -> Pattern a -> Maybe Env
matchPat v (PVar _ x) = Just (M.singleton x v)
matchPat _ (PWildcard _) = Just M.empty
matchPat (ConstVal c args) (PConst _ c' pats)
  | c == c' && length args == length pats = M.unions <$> zipWithM matchPat args pats
matchPat _ _ = Nothing
