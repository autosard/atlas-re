module Normalization where

import Ast
import Control.Monad.State (State, foldM, get, put, evalState)
import Typing.Type
import Primitive(Id, enumId)

type Norm = State Int

normalizeMod :: TypedModule -> TypedModule
normalizeMod m = runNorm $ nmModule m

normalizeExpr :: TypedExpr -> TypedExpr
normalizeExpr e = runNorm $ nmExpr e

runNorm :: Norm a -> a
runNorm nm = evalState nm 0

newVar :: Norm Id
newVar = do
  i <- get
  put (i + 1)
  return (enumId i)

nmModule :: TypedModule -> Norm TypedModule
nmModule = mapM nmFunDef

nmFunDef :: TypedFunDef -> Norm TypedFunDef
nmFunDef (FunDef ann id args body) = do
  body' <- nmExpr body
  return $ FunDef ann id args body'

nmExpr :: TypedExpr -> Norm TypedExpr
nmExpr e = do
  (hole, e') <- nmExpr' e
  return $ hole e'

nmExpr' :: TypedExpr -> Norm (HoleExpr, TypedExpr)
nmExpr' app@(AppAnn ann id args) = do
  normedArgs <- mapM nmExpr' args
  (hole, args') <- nmBinds (getType app) normedArgs
  return (hole, AppAnn ann id args')
nmExpr' match@(MatchAnn ann e arms) = do
  normedArms <- mapM nmMatchArm arms
  (hole, e') <- nmBind (getType match) (id, e)
  return (hole, MatchAnn ann e' normedArms)
nmExpr' e@(IteAnn ann e1@(Coin _) e2 e3) = do
  (holeE2, e2') <- nmExpr' e2
  (holeE3, e3') <- nmExpr' e3
  return (id, IteAnn ann e1 (holeE2 e2') (holeE3 e3'))
nmExpr' ite@(IteAnn ann e1 e2 e3) = do
  (holeE2, e2') <- nmExpr' e2
  (holeE3, e3') <- nmExpr' e3
  (holeE1, e1') <- nmBind (getType ite) (id, e1)
  return (holeE1, IteAnn ann e1' (holeE2 e2') (holeE3 e3'))
nmExpr' const@(ConstAnn ann id args) = do
  normedArgs <- mapM nmExpr' args
  (hole, args') <- nmBinds (getType const) normedArgs
  return (hole, ConstAnn ann id args')
nmExpr' (TickAnn ann c e) = do
  (hole, e') <- nmExpr' e
  return (id, TickAnn ann c (hole e'))
nmExpr' e = return (id, e)

nmMatchArm :: TypedMatchArm -> Norm TypedMatchArm
nmMatchArm (MatchArmAnn ann pat e) = do
  e' <- nmExpr e
  return $ MatchArmAnn ann pat e'

type HoleExpr = TypedExpr -> TypedExpr

srcForBind :: TypedExpr -> ExprSrc
srcForBind e = case (teSrc . getAnn) e of
  (Loc pos) -> DerivedFrom pos
  (DerivedFrom pos) -> DerivedFrom pos


letHole :: TypedExpr -> Id -> Type -> HoleExpr
letHole e v t = LetAnn (TypedExprAnn src t) v e
  where src = srcForBind e

nmBind :: Type -> (HoleExpr, TypedExpr) -> Norm (HoleExpr, TypedExpr)
nmBind t (holeE, e)
  | isImmediate e = return (id, e)
  | otherwise = do
      v <- newVar
      let hole = letHole e v t
      let ann = TypedExprAnn src (getType e)
      return (holeE . hole, VarAnn ann v)
        where src = srcForBind e
    

nmBinds :: Type -> [(HoleExpr, TypedExpr)] -> Norm (HoleExpr, [TypedExpr])
nmBinds t exps = foldM go (id, []) =<< mapM (nmBind t) exps
  where go (hole, exps) (hole', exp) = return (hole . hole', exps ++ [exp])

isImmediate :: Expr a -> Bool
isImmediate (Var _) = True
isImmediate _ = False


