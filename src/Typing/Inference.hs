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

import qualified Data.List as L
  
import Typing.Type
    ( fn, Tycon(Prod, Num, Bool, Arrow), Type(..), Tyvar(..) )
import Typing.Subst
import Typing.Scheme
import Ast
import Primitive(Id, enumId)
import Text.Megaparsec(SourcePos(sourceName, sourceLine, sourceColumn))
import Text.Megaparsec.Pos(unPos)
import SourceError
import Constants

import qualified Debug.Trace(trace)
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

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

litScheme :: Literal -> Scheme
litScheme (LitNum _) = Forall 0 (TAp Num [])

tiPatternVar :: Infer PatternVar (Context, Type)
tiPatternVar ctx (Id id) = do
  v <- newTVar
  return (M.insert id (Forall 0 v) ctx, v)
tiPatternVar ctx WildcardVar = do
  t <- newTVar
  return (M.empty, t)

tiPattern :: Infer ParsedPattern (Context, TypedPattern)
tiPattern ctx (ConstPat ann id vars) = do
  tp <- newTVar
  constT <- instScheme (constType id)
  (ctxs, varTs) <- mapAndUnzipM (tiPatternVar ctx) vars
  unify constT (varTs `fn` tp)
  let ann' = extendWithType tp ann
  return (M.unions (ctxs ++ [ctx]), ConstPat ann' id vars)
tiPattern ctx (PatAlias ann id) = do
  v <- newTVar
  let ann' = extendWithType v ann
  return (M.insert id (Forall 0 v) ctx, PatAlias ann' id)
tiPattern ctx (PatWildcard ann) = do
  v <- newTVar
  let ann' = extendWithType v ann
  return (ctx, PatWildcard ann')

tiMatchArm :: Infer ParsedMatchArm TypedMatchArm
tiMatchArm ctx arm@(MatchArmAnn ann pat e) = do
  trace arm
  (ctx', pat') <- tiPattern ctx pat
  e' <- tiExpr ctx' e
  untrace arm
  let ann' = extendWithType (getType e') ann 
  return $ MatchArmAnn ann' pat' e'

tiExpr :: Infer ParsedExpr TypedExpr
tiExpr ctx e = do
  trace e
  e' <- tiExpr' ctx e
  untrace e
  return e'


tiExpr' :: Infer ParsedExpr TypedExpr
tiExpr' ctx (VarAnn ann id) = do
  sc <- find id ctx
  t <- instScheme sc
  let ann' = extendWithType t ann
  return $ VarAnn ann' id
tiExpr' ctx (ConstAnn ann id args) = do
  to <- newTVar
  let sc = constType id
  tConst <- instScheme sc
  args' <- mapM (tiExpr ctx) args
  let tArgs = map getType args'
  unify tConst (tArgs `fn` to)
  let ann' = extendWithType to ann 
  return $ ConstAnn ann' id args'
tiExpr' ctx (LitAnn ann l) = do
  let sc = litScheme l
  t <- instScheme sc
  let ann' = extendWithType t ann
  return $ LitAnn ann' l
tiExpr' ctx (IteAnn ann e1 e2 e3) = do
  r <- newTVar
  
  e1' <- tiExpr ctx e1
  let t1 = getType e1'
  trace e1
  unify (TAp Bool []) t1
  untrace e1
  
  e2' <- tiExpr ctx e2
  let t2 = getType e2'
  trace e2
  unify r t2
  untrace e2
  
  e3' <- tiExpr ctx e3
  let t3 = getType e3'
  trace e3
  unify r t3
  untrace e2
  
  let ann' = extendWithType r ann
  return $ IteAnn ann' e1' e2' e3'
tiExpr' ctx (MatchAnn ann e arms) = do
  r <- newTVar
  e' <- tiExpr ctx e
  let te = getType e'
  arms' <- mapM (tiMatchArm ctx) arms
  mapM_ (unifyWithArm (te, r)) arms'
  let ann' = extendWithType r ann
  return $ MatchAnn ann' e' arms'
  where unifyWithArm (tp, te) (MatchArm pat e) = do
          unify tp $ getType pat
          unify te $ getType e
tiExpr' ctx (AppAnn ann id args) = do
  to <- newTVar
  scFun <- find id ctx
  tFun <- instScheme scFun
  args' <- mapM (tiExpr ctx) args
  let tArgs = map getType args'
  unify tFun (tArgs `fn` to)
  let ann' = extendWithType to ann
  return $ AppAnn ann' id args'
tiExpr' ctx (LetAnn ann x e1 e2) = do
  e1' <- tiExpr ctx e1
  let tx = getType e1'
  s <- gets subst
  let tx' = apply s tx
  let fs = tv (apply s ctx)
  let gs = tv tx' L.\\ fs
  let ctx' = M.insert x (quantify gs tx) ctx
  e2' <- tiExpr ctx' e2
  let te2 = getType e2'
  
  let ann' = extendWithType te2 ann
  return $ LetAnn ann' x e1' e2'
tiExpr' ctx (TickAnn ann c e) = do
  e' <- tiExpr ctx e
  let t = getType e'
  let ann' = extendWithType t ann
  return $ TickAnn ann' c e'
tiExpr' ctx (CoinAnn ann p) = do
  t <- instScheme boolSc
  let ann' = extendWithType t ann
  return $ CoinAnn ann' p

funArgTypes :: Type -> [Type]
funArgTypes (TAp Arrow [TAp Prod ts, _]) = ts
funArgTypes _ = error "cannot extract arg types from non-function type."

tiFun :: Infer ParsedFunDef (Type, TypedExpr)
tiFun ctx (FunDef ann id args exp) = do
  argVars <- mapM (const newTVar) args
  let argSchemes = map toScheme argVars
  let ctx' = M.fromList $ zip args argSchemes
  let ctx'' = ctx' `M.union` ctx
  exp' <- tiExpr ctx'' exp
  let te = argVars `fn` getType exp'
  return (te, exp')

tiApply :: Infer TypedExpr TypedExpr
tiApply ctx e = do
  s <- gets subst
  return $ apply s e

tiProg :: Infer ParsedModule TypedModule
tiProg ctx defs = do
  ctx' <- initCtx defs
  
  (ts, bodies) <- mapAndUnzipM (tiFun ctx') defs
  s <- gets subst
  let ts' = apply s ts
  let bodies' = apply s bodies
  let fs = tv (apply s ctx)
  let gss = map (\t -> tv t L.\\ fs) ts'
  --let ids = map (\(Fn id _ _) -> id) defs
  let qts = zipWith quantify gss ts'
  --let ctx' = M.fromList (zip ids qts) `M.union` ctx
  return $ map extendDef (zip3 defs qts bodies')
  where extendAnn t ann = TypedFunAnn{
          tfType = t,
          tfResourceAnn = pfResourceAnn ann,
          tfLoc = pfLoc ann,
          tfFqn = pfFqn ann}
        extendDef :: (ParsedFunDef, Scheme, TypedExpr) -> TypedFunDef
        extendDef (FunDef ann id args e, t, e')
          = FunDef (extendAnn t ann) id args e'


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
  Just (e , _) -> getAnn e 
    

runTI :: TiState -> TI a -> (Either TypeError a, TiState)
runTI s ti = runState (runExceptT ti) s

evalTI :: TiState -> TI a -> Either TypeError a
evalTI s = fst . runTI s


infer :: TI a -> Either SourceError a
infer ti = case runTI initState ti of
  (Left e, s) -> Left $ SourceError (currentExpLoc s) (show e)
  (Right x, _) -> Right x
  where initState = TiState 0 nullSubst []

inferModule :: [ParsedFunDef] -> Either SourceError TypedModule
inferModule = infer . tiProg M.empty

inferExpr :: TypedModule -> ParsedExpr -> Either SourceError TypedExpr
inferExpr context expr = infer $ tiApply M.empty =<< tiExpr initCtx expr
  where initCtx = M.fromList $ map getScheme context
        getScheme (FunDef funAnn id _ _) = (id, tfType funAnn)
