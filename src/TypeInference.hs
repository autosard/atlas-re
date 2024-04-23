{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}

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
import Control.Monad.Identity (Identity)
import Text.Megaparsec(SourcePos(sourceName, sourceLine, sourceColumn))
import Text.Megaparsec.Pos(unPos)
import GHC.ExecutionStack (Location(functionName))

data TiState = TiState {
  idGen :: Int,
  subst :: Subst,
  expStack :: [ParsedExpr]}

data TypeError
  = TypeMismatch Type Type
  | OccursCheck Tyvar Type
  | UnboundIdentifier Id

instance Show TypeError where
  show (TypeMismatch expected actual) = "Couldn't match type '" ++ show expected ++ "' with '" ++ show actual ++ "'\n"
    ++ "\tExpected: " ++ show expected
    ++ "\n"
    ++ "\tActual: " ++ show actual
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
  put state{subst = s' @@ subst state}

type Context = Map Id Scheme

find :: Id -> Context -> TI Scheme
find id ctx = maybe (throwError (UnboundIdentifier id)) return (findMaybe id ctx)

findMaybe :: Id -> Context -> Maybe Scheme
findMaybe = M.lookup

newTVar :: TI Type
newTVar = do
  s <- lift get
  let v = Tyvar (enumId (idGen s))
  lift $ put s{idGen = idGen s + 1}
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
  let ts = A.listArray (0,len-1) vars
  return (inst ts t)

instance Types b => Types (Map a b) where
  apply s = M.map (apply s) 
  tv m = concatMap tv $ M.elems m

type Infer e t = Context -> e -> TI t

constScheme :: ParsedExpr -> Scheme
constScheme ConstTrue = boolT
constScheme ConstFalse = boolT
constScheme (ConstTuple {}) = tupleT
constScheme (ConstTreeNode {}) = treeT
constScheme ConstTreeLeaf = treeT

litScheme :: Literal -> Scheme
litScheme (LitNum _) = Forall 0 (TAp Num [])

tiConst :: Infer ParsedExpr Type
tiConst ctx (ConstTreeNode l v r) = do
  freshTreeT <- instScheme treeT
  let [valueType] = tv freshTreeT
  tl <- tiExpr ctx l 
  unify freshTreeT tl
  tv <- tiExpr ctx v
  unify (TVar valueType) tv
  tr <- tiExpr ctx r
  unify freshTreeT tr
  return freshTreeT
tiConst ctx ConstTreeLeaf = instScheme treeT
tiConst ctx (ConstTuple x y) = do
  freshTupleT <- instScheme tupleT
  let [a, b] = tv freshTupleT
  tx <- tiExpr ctx x
  unify (TVar a) tx
  ty <- tiExpr ctx y
  unify (TVar b) ty
  return freshTupleT
tiConst ctx ConstTrue = instScheme boolT
tiConst ctx ConstFalse = instScheme boolT
  

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
tiPattern ctx LeafPattern = (ctx,) <$> instScheme treeT
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
  
tiMatchArm :: Infer ParsedMatchArm (Type, Type)
tiMatchArm ctx (pat, e) = do
  (ctx', tp) <- tiPattern ctx pat
  te <- tiExpr ctx' e
  return (tp, te)

pushExp :: ParsedExpr -> TI ()
pushExp e = do
  s <- get
  put s{expStack = e:expStack s}

popExp :: TI ()
popExp = do
  s <- get
  put s{expStack = tail (expStack s)}

tiExpr :: Infer ParsedExpr Type
tiExpr ctx e = do
  pushExp e
  t <- tiExpr' ctx e
  popExp
  return t

tiExpr' :: Infer ParsedExpr Type
tiExpr' ctx e@(Var id) = do
  sc <- find id ctx
  instScheme sc
tiExpr' ctx const@(Const _ args) = tiConst ctx const
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
tiExpr' ctx (BExpr {}) = instScheme boolT
tiExpr' ctx (Let x e1 e2) = do
  tx <- tiExpr ctx e1
  let ctx' = M.insert x (Forall 0 tx) ctx
  tiExpr ctx e2
tiExpr' ctx (Tick _ e) = tiExpr ctx e
tiExpr' ctx (Coin _) = instScheme boolT

tiFunDef :: Infer ParsedFunDef Type
tiFunDef ctx (Fn id args exp) = do
  argVars <- mapM (\v -> (v,) . Forall 0 <$> newTVar) args
  let argVars' = M.fromList argVars
  let ctx' = argVars' `M.union` ctx
  inferedFunT <- tiExpr ctx' exp
  sc <- find id ctx
  funT <- instScheme sc
  unify funT inferedFunT
  return funT


tiProg :: Infer ParsedModule [(Id, Type)]
tiProg ctx defs = do
  let ctx' = initCtx defs
  ts <- mapM (\def@(Fn id _ _) -> (id,) <$> tiFunDef ctx' def) defs
  s <- gets subst
  return $ map (\pair -> apply s <$> pair) ts
  

initCtx :: [ParsedFunDef] -> Context
initCtx defs = M.fromList (map assumeType defs)
  where assumeType (FnParsed ann id args _) = case pfType ann of
          Just sc -> (id, sc)
          Nothing -> (id, nAryFn (length args))

showSrcPos :: SourcePos -> String
showSrcPos pos = let name = sourceName pos
                     line = unPos $ sourceLine pos
                     column = unPos $ sourceColumn pos
                 in 
                   name ++ ":" ++ show line ++ ":" ++ show column ++ ":"

showCurrentExp :: TiState -> String
showCurrentExp s = case uncons (expStack s) of
  Nothing -> "no expr"
  Just (e , _) -> let pos = exprAnn e in
    showSrcPos pos ++ " " ++ show e

runTypeInference :: [ParsedFunDef] -> [(Id, Type)]
runTypeInference defs = case runState state initState of
  (Left e, s) -> error $ showCurrentExp s ++ ": " ++ show e
  (Right context, s) -> context
  where initState = TiState 0 nullSubst []
        state = runExceptT (tiProg M.empty defs)
