{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module TypeInference where

import Control.Monad.State
import Control.Monad.Except
import Data.Map(Map)
import qualified Data.Map as M
import Data.Array(Array)
import qualified Data.Array as A
import Data.List(concatMap, uncons)
  
import Types
import Ast
import Primitive(Id)
import Data.Data (typeOf2)
import Text.Megaparsec (Stream(take1_))
import Control.Monad.Identity (Identity)

import Debug.Trace(trace)

data TiState = TiState {
  idGen :: Int,
  subst :: Subst,
  expStack :: [Expr]}

data TypeError
  = TypeMismatch Type Type
  | OccursCheck Tyvar Type
  | UnboundIdentifier Id

instance Show TypeError where
  show (TypeMismatch expected actual) = "Couldn't match type '" ++ show expected ++ "' with '" ++ show actual ++ "'\n"
    ++ "Expected: " ++ show expected
    ++ "Actual: " ++ show actual
  show (OccursCheck var t) = "Occurs check failed for '" ++ show var ++ "' in '" ++ show t ++ "'."
  show (UnboundIdentifier id) = "Unbound identifier: '" ++ show id ++ "'"
  
type TI = ExceptT TypeError (State TiState)

mgu :: Type -> Type -> TI Subst 
mgu (TAp c1 tsl) (TAp c2 tsr)
  | c1 == c2 && length tsl == length tsr
  = foldM mgu' nullSubst $ zip tsl tsr
  where mgu' s (l, r) = do
          s' <- mgu (apply  s l) (apply s r)
          return (s' @@ s)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu t1 t2 = throwError $ TypeMismatch t1 t2

varBind :: Tyvar -> Type -> TI Subst
varBind u t | t == TVar u = return nullSubst
            | u `elem` tv t = throwError $ OccursCheck u t
            | otherwise = return (u +-> t)

unify :: Type -> Type -> TI ()
unify t1 t2 = do
  s <- gets subst
  u <- mgu (apply s t1) (apply s t2)
  extSubst u
  
extSubst :: Subst -> TI ()
extSubst s' = do
  state <- get
  put state{subst = s' @@ (subst state)}

type Context = Map Id Scheme

find :: Id -> Context -> TI Scheme
find id ctx = maybe (throwError (UnboundIdentifier id)) return (M.lookup id ctx)

newTVar :: TI Type
newTVar = do
  s <- lift get
  let v = Tyvar (enumId (idGen s))
  lift $ put s{idGen = (idGen s) + 1}
  return (TVar v)

class Instantiate t where
  inst :: Array Int Type -> t -> t

instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
  
instance Instantiate Type where
  inst ts (TAp c args) = TAp c (inst ts args)
  inst ts (TGen i) = ts A.! i
  inst ts t = t

instScheme :: Scheme -> TI Type
instScheme (Forall len t) = do
  vars <- mapM (const newTVar) [0..len-1]
  let ts = (A.listArray (0,len-1) vars)
  return (inst ts t)

instance Types b => Types (Map a b) where
  apply s = M.map (apply s) 
  tv m = concatMap tv $ M.elems m

type Infer e t = Context -> e -> TI t

constScheme ::  DataConstructor -> Scheme
constScheme (BooleanConstructor _) = boolT
constScheme (TupleConstructor _) = tupleT
constScheme (TreeConstructor _) = treeT

litScheme :: Literal -> Scheme
litScheme (LitNum _) = Forall 0 (TAp Num [])

tiPatternVar :: Infer PatternVar (Context, Type)
tiPatternVar ctx (Id id) = do
  v <- newTVar
  return (M.insert id (Forall 0 v) ctx, v)
tiPatternVar ctx WildcardVar = do
  t <- newTVar
  return (M.empty, t)

tiPattern :: Infer Pattern (Context, Type)
tiPattern ctx (TreePattern l v r) = do
  freshTreeT <- instScheme treeT
  let [valueType] = tv freshTreeT
  (cl, tl) <- tiPatternVar ctx l 
  unify freshTreeT tl
  (cv, tv) <- tiPatternVar ctx v
  unify (TVar valueType) tv
  (cr, tr) <- tiPatternVar ctx r
  unify freshTreeT tr
  return (M.unions [cl, cv, cr, ctx], freshTreeT)
tiPattern ctx LeafPattern = (M.empty,) <$> instScheme treeT
tiPattern ctx (TuplePattern v1 v2) = do
  freshTupleT <- instScheme tupleT
  let [a, b] = tv freshTupleT
  (ca, t1) <- tiPatternVar ctx v1
  unify (TVar a) t1
  (cb, t2) <- tiPatternVar ctx v2
  unify (TVar b) t2
  return (M.unions [ca, cb, ctx], freshTupleT)
tiPattern ctx (Alias id) = do
  v <- newTVar
  return (M.insert id (Forall 0 v) ctx, v)
tiPattern ctx WildcardPattern = (ctx,) <$> newTVar
  
tiMatchArm :: Infer MatchArm (Type, Type)
tiMatchArm ctx (pat, e) = do
  (ctx', tp) <- tiPattern ctx pat
  te <- tiExpr ctx' e
  return (tp, te)

pushExp :: Expr -> TI ()
pushExp e = do
  s <- get
  put s{expStack = e:expStack s}

popExp :: TI ()
popExp = do
  s <- get
  put s{expStack = tail (expStack s)}

tiExpr :: Infer Expr Type
tiExpr ctx e = do
  pushExp e
  t <- tiExpr' ctx e
  popExp
  return t

tiExpr' :: Infer Expr Type
tiExpr' ctx e@(Var id) = do
  sc <- find id ctx
  instScheme sc
tiExpr' ctx (ConstructorExpr const) = do
  let sc = constScheme const
  instScheme sc
tiExpr' ctx (Lit l) = do
  let sc = litScheme l
  instScheme sc
tiExpr' ctx (Ite e1 e2 e3) = do
  r <- newTVar
  t1 <- tiExpr ctx e1
  unify (TAp Bool []) t1
  t2 <- tiExpr ctx e2
  unify r t2
  t3 <- tiExpr ctx e3
  unify r t3
  return r
tiExpr' ctx (Match e arms) = do
  r <- newTVar
  te <- tiExpr ctx e
  mapM_ (fmap (unifyWithArm (te, r)) . tiMatchArm ctx) arms
  return r
  where unifyWithArm (tp1, te1) (tp2, te2) = do
          unify tp1 tp2
          unify te1 te2
tiExpr' ctx (App id exps) = do
  scFun <- find id ctx
  tFun <- instScheme scFun
  tArgs <- instScheme $ nAryFn (length exps)
  unify tFun tArgs
  return tFun
tiExpr' ctx (BExpr _ _ _) = instScheme boolT
tiExpr' ctx (Let x e1 e2) = do
  tx <- tiExpr ctx e1
  let ctx' = M.insert x (Forall 0 tx) ctx
  tiExpr ctx e2
tiExpr' ctx (Tick _ e) = tiExpr ctx e
tiExpr' ctx (Coin _) = instScheme boolT
tiExpr' ctx (Fn args exp) = do
  argVars <- mapM (\v -> (v,) <$> (Forall 0 <$> newTVar)) args
  let argVars' = M.fromList argVars
  let ctx' = argVars' `M.union` ctx
  tiExpr ctx' exp
  -- TODO unify 


traceShow1 v = trace (show v) v

tiProg :: Infer [FunctionDefinition] Context
tiProg ctx defs = do
  ctx' <- initCtx defs
  ts <- mapM (tiExpr ctx' . funBody) defs
  s <- gets subst
  return (apply s ctx')
  

initCtx :: [FunctionDefinition] -> TI Context
initCtx defs = M.fromList <$> assumps
  where assump def = case sigType <$> funSignature def of
          Just t -> pure (funName def, t)
          Nothing -> (funName def,) <$> (Forall 0 <$> newTVar)
        assumps = mapM assump defs

--showSrcPos :: SourcePos -> String
--showSrcPos SourcePos{..} = show sourceName ++ ":" ++ show sourceLine ++ ":" ++ show sourceColumn ++ ":"

showCurrentExp :: TiState -> String
showCurrentExp s = case uncons (expStack s) of
  Nothing -> "no expr"
  Just (e, _) -> show e
  --Just (SrcExpr e pos, _) -> showSourcePos pos ++ " " ++ show e

runTypeInference :: [FunctionDefinition] -> Context
runTypeInference defs = case runState state initState of
  (Left e, s) -> error $ (showCurrentExp s) ++ ": " ++ show e
  (Right context, s) -> context
  where initState = TiState 0 nullSubst []
        state = runExceptT (tiProg M.empty defs)
