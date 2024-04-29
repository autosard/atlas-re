{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module Typing.Inference where

import Control.Monad.State
import Control.Monad.Except
import Data.Map(Map)
import qualified Data.Map as M
import Data.Array(Array)
import qualified Data.Array as A
import Data.List(uncons)
import System.Exit

import qualified Data.List as L
  
import Typing.Type
import Typing.Subst
import Typing.Scheme
import Ast
import Primitive(Id, enumId)
import Text.Megaparsec(SourcePos(sourceName, sourceLine, sourceColumn))
import Text.Megaparsec.Pos(unPos)
import SourceError

data TiState = TiState {
  idGen :: Int,
  subst :: Subst,
  traceStack :: [ParsedSyntax]}

class Traceable a where
  trace :: a -> TI ()

instance Traceable ParsedExpr where
  trace e = pushSyn $ SynExpr e

instance Traceable ParsedMatchArm where
  trace arm = pushSyn $ SynArm arm

instance Traceable ParsedPattern where
  trace p = pushSyn $ SynPat p

untrace :: a -> TI ()
untrace _ = popSyn

pushSyn :: ParsedSyntax -> TI ()
pushSyn e = do
  s <- get
  put s{traceStack = e:traceStack s}

popSyn :: TI ()
popSyn = do
  s <- get
  put s{traceStack = tail (traceStack s)}



data TypeError
  = TypeMismatch Type Type
  | OccursCheck Tyvar Type
  | UnboundIdentifier Id
  deriving Eq

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


instance Types b => Types (Map a b) where
  apply :: Types b => Subst -> Map a b -> Map a b
  apply s = M.map (apply s) 
  tv m = concatMap tv $ M.elems m

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

tiPattern :: Infer ParsedPattern (Context, Type)
tiPattern ctx (PatTreeNode l v r) = do
  freshTreeT <- instScheme treeT
  let [valueType] = tv freshTreeT
  (cl, tl) <- tiPatternVar ctx l 
  unify freshTreeT tl
  (cv, tv) <- tiPatternVar ctx v
  unify (TVar valueType) tv
  (cr, tr) <- tiPatternVar ctx r
  unify freshTreeT tr
  return (M.unions [cl, cv, cr, ctx], freshTreeT)
tiPattern ctx PatTreeLeaf = (ctx,) <$> instScheme treeT
tiPattern ctx (PatTuple v1 v2) = do
  freshTupleT <- instScheme tupleT
  let [a, b] = tv freshTupleT
  (ca, t1) <- tiPatternVar ctx v1
  unify (TVar a) t1
  (cb, t2) <- tiPatternVar ctx v2
  unify (TVar b) t2
  return (M.unions [ca, cb, ctx], freshTupleT)
tiPattern ctx (PatAlias id) = do
  v <- newTVar
  return (M.insert id (Forall 0 v) ctx, v)
tiPattern ctx PatWildcard = (ctx,) <$> newTVar

tiMatchArm :: Infer ParsedMatchArm (Type, Type)
tiMatchArm ctx arm = do
  trace arm
  (tp, te) <- tiMatchArm' ctx arm
  untrace arm
  return (tp, te)


tiMatchArm' :: Infer ParsedMatchArm (Type, Type)
tiMatchArm' ctx (MatchArm pat e) = do
  (ctx', tp) <- tiPattern ctx pat
  te <- tiExpr ctx' e
  return (tp, te)


tiExpr :: Infer ParsedExpr Type
tiExpr ctx e = do
  trace e
  t <- tiExpr' ctx e
  untrace e
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
  trace e1
  unify (TAp Bool []) t1
  untrace e1
  t2 <- tiExpr ctx e2
  trace e2
  unify r t2
  untrace e2
  t3 <- tiExpr ctx e3
  trace e3
  unify r t3
  untrace e2
  return r
tiExpr' ctx (Match e arms) = do
  r <- newTVar
  te <- tiExpr ctx e
  armTs <- mapM (tiMatchArm ctx) arms
  mapM_ (unifyWithArm (te, r)) armTs
  return r
  where unifyWithArm (tp1, te1) (tp2, te2) = do
          unify tp1 tp2
          unify te1 te2
tiExpr' ctx (App id exps) = do
  to <- newTVar
  scFun <- find id ctx
  tFun <- instScheme scFun
  tArgs <- mapM (tiExpr ctx) exps
  unify tFun (tArgs `fn` to)
  return to
tiExpr' ctx (BExpr {}) = instScheme boolT
tiExpr' ctx (Let x e1 e2) = do
  tx <- tiExpr ctx e1
  s <- gets subst
  let tx' = apply s tx
  let fs = tv (apply s ctx)
  let gs = tv tx' L.\\ fs
  let ctx' = M.insert x (quantify gs tx) ctx
  tiExpr ctx' e2
tiExpr' ctx (Tick _ e) = tiExpr ctx e
tiExpr' ctx (Coin _) = instScheme boolT

funArgTypes :: Type -> [Type]
funArgTypes (TAp Arrow [TAp Prod ts, _]) = ts
funArgTypes _ = error "cannot extract arg types from non-function type."

tiFun :: Infer ParsedFunDef Type
tiFun ctx (Fn _ args exp) = do
  argVars <- mapM (const newTVar) args
  let argSchemes = map toScheme argVars
  let ctx' = M.fromList $ zip args argSchemes
  let ctx'' = ctx' `M.union` ctx
  te <- tiExpr ctx'' exp
  return $ argVars `fn` te


tiProg :: Infer ParsedModule Context
tiProg ctx defs = do
  ctx' <- initCtx defs
  
  ts <- mapM (tiFun ctx') defs
  s <- gets subst
  let ts' = apply s ts
  let fs = tv (apply s ctx)
  let gss = map (\t -> tv t L.\\ fs) ts'
  let ids = map (\(Fn id _ _) -> id) defs
  let qts = zipWith quantify gss ts'
  let ctx' = M.fromList (zip ids qts) `M.union` ctx
  return ctx'
  

initCtx :: [ParsedFunDef] -> TI Context
initCtx defs = M.fromList <$> mapM assumeType defs
  where assumeType (FnParsed ann id args _) = case pfType ann of
          Just sc -> (id,) . toScheme <$> instScheme sc
          Nothing -> (id,) . toScheme <$> newTVar

showSrcPos :: SourcePos -> String
showSrcPos pos = let name = sourceName pos
                     line = unPos $ sourceLine pos
                     column = unPos $ sourceColumn pos
                 in 
                   name ++ ":" ++ show line ++ ":" ++ show column ++ ":"

currentExpLoc :: TiState -> SourcePos
currentExpLoc s = case uncons (traceStack s) of
  Nothing -> error "pop from empty syntax stack"
  Just (e , _) -> synAnn e 
    

runTI :: TiState -> TI a -> (Either TypeError a, TiState)
runTI s ti = runState (runExceptT ti) s

evalTI :: TiState -> TI a -> Either TypeError a
evalTI s = fst . runTI s

runTypeInference :: [ParsedFunDef] -> IO Context
runTypeInference defs = case runTI initState (tiProg M.empty defs) of
  (Left e, s) -> die =<< printSrcError (SourceError (currentExpLoc s) (show e))
  (Right context, _) -> return context
  where initState = TiState 0 nullSubst []

