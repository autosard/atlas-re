{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module Typing.Inference where

import Control.Monad.State
import Control.Monad.Except
import Data.Map(Map)
import qualified Data.Map as M
import Data.Array(Array)
import qualified Data.Array as A
import Control.Monad.Extra(mapAndUnzipM, foldM)
import Data.List(uncons)
import Lens.Micro.Platform

import qualified Data.List as L
import qualified Data.Text as T
  
import Typing.Type(Type(..),fn, unprod, tCurry)
import Typing.Subst
import Typing.Scheme
import Syntax.Ast
import Primitive(Id, enumId, prettyPrint)
import Text.Megaparsec(SourcePos(sourceName, sourceLine, sourceColumn))
import Text.Megaparsec.Pos(unPos)
import SourceError
import Syntax.Constants


data TiState = TiState {
  idGen :: Int,
  subst :: Subst,
  traceStack :: [Syntax Elaborated]}

class Traceable a where
  trace :: a -> TI ()

instance Traceable (Expr Elaborated) where
  trace e = pushSyn $ SynExpr e

instance Traceable (MatchArm Elaborated) where
  trace arm = pushSyn $ SynArm arm

instance Traceable (Pattern Elaborated) where
  trace p = pushSyn $ SynPat p

untrace :: a -> TI ()
untrace _ = popSyn

pushSyn :: Syntax Elaborated -> TI ()
pushSyn e = do
  s <- get
  put s{traceStack = e:traceStack s}

popSyn :: TI ()
popSyn = do
  s <- get
  put s{traceStack = tail (traceStack s)}



data TypeError
  = TypeMismatch Type Type
  | OccursCheck Id Type
  | UnboundIdentifier Id
  | UnknownDataConstructor Id
  deriving Eq

instance Show TypeError where
  show (TypeMismatch expected actual) = "Couldn't match type '" ++ prettyPrint expected ++ "' with '" ++ prettyPrint actual ++ "'\n"
    ++ "\tExpected: " ++ prettyPrint expected
    ++ "\n"
    ++ "\tActual: " ++ prettyPrint actual
  show (OccursCheck var t) = "Occurs check failed for '" ++ T.unpack var ++ "' in '" ++ show t ++ "'."
  show (UnboundIdentifier id) = "Unbound identifier: '" ++ T.unpack id ++ "'"
  show (UnknownDataConstructor id) = "Unknown data constructor: '" ++ T.unpack id ++ "'"
  
type TI = ExceptT TypeError (State TiState)

mgu :: Type -> Type -> TI Subst 
mgu (TAp c1 tsl) (TAp c2 tsr)
  | c1 == c2 && length tsl == length tsr
  = foldM mgu' nullSubst $ zip tsl tsr
  where mgu' s (l, r) = do
          s' <- mgu (apply  s l) (apply s r)
          return (s' @@ s)
mgu (TFun l1 r1) (TFun l2 r2) = do
  s1 <- mgu l1 l2
  s2 <- mgu (apply s1 r1) (apply s1 r2)
  return $ s2 @@ s1
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu t1 t2 = throwError $ TypeMismatch t1 t2

varBind :: Id -> Type -> TI Subst
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


type CtorEnv = Map Id Scheme
type Context = Map Id Scheme

buildCtorEnv :: DataEnv -> CtorEnv
buildCtorEnv dEnv = let cis = concatMap diCtors (M.elems dEnv) in
  M.fromList $ map (\ci -> (ciName ci, ciType ci)) cis

lookupCtor :: Id -> CtorEnv -> TI Scheme
lookupCtor id cEnv = maybe (throwError $ UnknownDataConstructor id) return (cEnv M.!? id)

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
  let v = enumId (idGen s)
  lift $ put s{idGen = idGen s + 1}
  return (TVar v)

class Instantiate t where
  inst :: Array Int Type -> t -> t

instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
  
instance Instantiate Type where
  inst ts (TAp c args) = TAp c (inst ts args)
  inst ts (TGen i) = ts A.! i
  inst ts (TFun t1 t2) = TFun (inst ts t1) (inst ts t2)
  inst ts t = t

instScheme :: Scheme -> TI Type
instScheme (Forall len t) = do
  vars <- mapM (const newTVar) [0..len-1]
  let ts = A.listArray (0,len-1) vars
  return (inst ts t)


type Infer e t = Context -> CtorEnv -> e -> TI t

tiPattern :: Infer (Pattern Elaborated) (Context, Pattern Typed)
tiPattern ctx cEnv (PConst ann id ps) = do
  tp <- newTVar
  constT <- instScheme =<< lookupCtor id cEnv
  (ctxs, ps') <- mapAndUnzipM (tiPattern ctx cEnv) ps
  let psTs = map getType ps'
  unify constT (psTs `tCurry` tp)
  let ann' = extendWithType tp ann
  return (M.unions (ctxs ++ [ctx]), PConst ann' id ps')
tiPattern ctx _ (PVar ann id) = do
  v <- newTVar
  let ann' = extendWithType v ann
  return (M.insert id (Forall 0 v) ctx, PVar ann' id)
tiPattern ctx _ (PWildcard ann) = do
  v <- newTVar
  let ann' = extendWithType v ann
  return (ctx, PWildcard ann')

tiMatchArm :: Infer (MatchArm Elaborated) (MatchArm Typed)
tiMatchArm ctx cEnv arm@(MatchArmAnn ann pat e) = do
  trace arm
  (ctx', pat') <- tiPattern ctx cEnv pat
  e' <- tiExpr ctx' cEnv e
  untrace arm
  let ann' = extendWithType (getType e') ann 
  return $ MatchArmAnn ann' pat' e'

tiExpr :: Infer (Expr Elaborated) (Expr Typed)
tiExpr ctx cEnv e = do
  trace e
  e' <- tiExpr' ctx cEnv e
  untrace e
  return e'


tiExpr' :: Infer (Expr Elaborated) (Expr Typed)
tiExpr' ctx _ (LitAnn ann lit) = do
  let t = case lit of
            LNat _ -> TAp "Nat" []
            LRat _ -> TAp "Rat" []
            LString _ -> TAp "String" []
  let ann' = extendWithType t ann
  return $ LitAnn ann' lit
tiExpr' ctx _ (VarAnn ann id) = do
  sc <- find id ctx
  t <- instScheme sc
  let ann' = extendWithType t ann
  return $ VarAnn ann' id
tiExpr' ctx cEnv (ConstAnn ann id args) = do
  to <- newTVar
  sc <- lookupCtor id cEnv
  tConst <- instScheme sc
  args' <- mapM (tiExpr ctx cEnv) args
  let tArgs = map getType args'
  unify tConst (tArgs `tCurry` to)
  let ann' = extendWithType to ann 
  return $ ConstAnn ann' id args'
tiExpr' ctx cEnv (IteAnn ann e1 e2 e3) = do
  r <- newTVar
  
  e1' <- tiExpr ctx cEnv e1
  let t1 = getType e1'
  trace e1
  unify (TAp "Bool" []) t1
  untrace e1
  
  e2' <- tiExpr ctx cEnv e2
  let t2 = getType e2'
  trace e2
  unify r t2
  untrace e2
  
  e3' <- tiExpr ctx cEnv e3
  let t3 = getType e3'
  trace e3
  unify r t3
  untrace e2
  
  let ann' = extendWithType r ann
  return $ IteAnn ann' e1' e2' e3'
tiExpr' ctx cEnv (MatchAnn ann e arms) = do
  r <- newTVar
  e' <- tiExpr ctx cEnv e
  let te = getType e'
  arms' <- mapM (tiMatchArm ctx cEnv) arms
  mapM_ (unifyWithArm (te, r)) arms'
  let ann' = extendWithType r ann
  return $ MatchAnn ann' e' arms'
  where unifyWithArm (tp, te) (MatchArm pat e) = do
          unify tp $ getType pat
          unify te $ getType e
tiExpr' ctx cEnv (AppAnn ann id args) = do
  to <- newTVar
  scFun <- find id ctx
  tFun <- instScheme scFun
  args' <- mapM (tiExpr ctx cEnv) args
  let tArgs = map getType args'
  unify tFun (tArgs `fn` to)
  let ann' = extendWithType to ann
  return $ AppAnn ann' id args'
tiExpr' ctx cEnv (LetAnn ann x e1 e2) = do
  e1' <- tiExpr ctx cEnv e1
  let tx = getType e1'
  s <- gets subst
  let tx' = apply s tx
  let fs = tv (apply s ctx)
  let gs = tv tx' L.\\ fs
  let ctx' = M.insert x (quantify gs tx) ctx
  e2' <- tiExpr ctx' cEnv e2
  let te2 = getType e2'
  
  let ann' = extendWithType te2 ann
  return $ LetAnn ann' x e1' e2'
tiExpr' ctx cEnv (TickAnn ann c e) = do
  e' <- tiExpr ctx cEnv e
  let t = getType e'
  let ann' = extendWithType t ann
  return $ TickAnn ann' c e'
tiExpr' ctx cEnv (CoinAnn ann p) = do
  let t = TAp "Bool" []
  let ann' = extendWithType t ann
  return $ CoinAnn ann' p

-- funArgTypes :: Type -> [Type]
-- funArgTypes (TFun t _]) = ts
-- funArgTypes _ = error "cannot extract arg types from non-function type."

data TypedFunResult = TypedFunResult
  { _tfrId   :: Id
  , _tfrArgs  :: [Id]
  , _tfrType :: Type
  , _tfrBody :: Expr Typed
  }

makeLenses ''TypedFunResult  

instance Types TypedFunResult where
  apply s =
    over tfrType (apply s)
    . over tfrBody (apply s)
  tv tfr = tv (tfr^.tfrType) ++ tv (tfr^.tfrBody)

tiFun :: Infer (FunDef Elaborated) TypedFunResult
tiFun ctx cEnv fun = do
  (tsFrom, tTo) <- case toType <$> ctx M.!? (fun^.funName) of
    Just (TFun from to) -> return (unprod from, to)
    Just (TVar _) -> do
      from <- mapM (const newTVar) (fun^.funArgs)
      to <- newTVar
      return (from, to)
    Nothing -> error "function not in context"
  let argSchemes = map toScheme tsFrom
  let ctx' = M.fromList $ zip (fun^.funArgs) argSchemes
  let ctx'' = ctx' `M.union` ctx
  trace (fun^.funBody)
  exp' <- tiExpr ctx'' cEnv (fun^.funBody)
  unify (getType exp') tTo
  untrace (fun^.funBody)
  let te = tsFrom `fn` getType exp'
  return $ TypedFunResult (fun^.funName) (fun^.funArgs) te exp'

  

tiApply :: Infer TypedExpr TypedExpr
tiApply ctx _ e = do
  s <- gets subst
  return $ apply s e

data QuantifiedFunResult = QuantifiedFunResult
  { qfrId   :: Id
  , qfrArgs :: [Id]
  , qfrType :: Scheme
  , qfrBody :: Expr Typed}

generalizeFunResult :: [Id] -> TypedFunResult -> QuantifiedFunResult
generalizeFunResult fs tfr = 
  QuantifiedFunResult
    { qfrId   = tfr ^. tfrId
    , qfrArgs   = tfr ^. tfrArgs
    , qfrType = quantify gs (tfr ^. tfrType)
    , qfrBody = tfr ^. tfrBody
    }
  where
    gs = tv (tfr ^. tfrType) L.\\ fs

  
tiProg :: Infer (Program Elaborated) (Program Typed)
tiProg ctx tEnv prog = do
  ctx' <- M.union <$> initCtx prog <*> return builtInFunTypes
  results <- mapM (tiFun ctx' tEnv) (fns prog)
  s <- gets subst
  let fs = tv (apply s ctx')
  let results' = map (generalizeFunResult fs) . apply s $ results
  let funDefs = M.fromList $
        [ (qfrId r, FunDef (qfrId r) (qfrArgs r) (qfrBody r))
        | r <- results']
  let sigs = M.fromList
        [ let cost = case (prog^.pSig) M.!? qfrId r of
                Just sig -> sig^.costSig
                Nothing -> Nothing
          in (qfrId r, FunSig (qfrType r) cost)
        | r <- results' ]
  return $ prog
      & pFunDefs .~ funDefs
      & pSig     .~ sigs

initCtx :: Program Elaborated -> TI Context
initCtx prog = traverse assumeType (prog^.pFunDefs)
  where assumeType fun
          = case (prog^.pSig) M.!? (fun^.funName) of
              Just sig -> let sc = sig^.typeSig in
                toScheme <$> instScheme sc
              Nothing -> toScheme <$> newTVar

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


infer :: TI a -> Either (SourceError TypeError) a
infer ti = case runTI initState ti of
  (Left e, s) -> Left $ SourceError (currentExpLoc s) e
  (Right x, _) -> Right x
  where initState = TiState 0 nullSubst []

inferProgram :: Program Elaborated -> Either (SourceError TypeError) (Program Typed)
inferProgram p = (infer . tiProg M.empty (cTorEnvForProg p)) p

-- | left-biased union (does not overide builtins)
cTorEnvForProg :: Program a -> CtorEnv
cTorEnvForProg p = buildCtorEnv $ M.union builtInDataDefs (p^.pDataEnv)

-- inferExpr :: TypedProgram -> ParsedExpr -> Either SourceError TypedExpr
-- inferExpr p expr = infer $ tiApply M.empty cEnv =<< tiExpr initCtx cEnv expr
--   where initCtx = M.fromList $ map getScheme (fns p)
--         getScheme fun = (id, tfType funAnn)
--         cEnv = cTorEnvForProg p
