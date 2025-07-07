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
nmModule = modMapM nmFunDef

nmFunDef :: TypedFunDef -> Norm TypedFunDef
nmFunDef (FunDef ann id args body) = do
  body' <- nmExpr body
  return $ FunDef ann id args body'

nmExpr :: TypedExpr -> Norm TypedExpr
nmExpr e = do
  (hole, e') <- nmExpr' e
  return $ hole (getType e') e'

nmExpr' :: TypedExpr -> Norm (HoleExpr, TypedExpr)
nmExpr' app@(AppAnn ann id args) = do
  normedArgs <- mapM nmExpr' args
  (hole, args') <- nmBinds normedArgs
  return (hole, AppAnn ann id args')
nmExpr' match@(MatchAnn ann e arms) = do
  normedArms <- mapM nmMatchArm arms
  (hole, e') <- nmBind (idHole, e)
  return (hole, MatchAnn ann e' normedArms)
nmExpr' e@(IteAnn ann e1@(Coin _) e2 e3) = do
  (holeE2, e2') <- nmExpr' e2
  (holeE3, e3') <- nmExpr' e3
  return (idHole, IteAnn ann e1
           (holeE2 (getType e2') e2')
           (holeE3 (getType e3') e3'))
nmExpr' ite@(IteAnn ann e1 e2 e3) = do
  (holeE2, e2') <- nmExpr' e2
  (holeE3, e3') <- nmExpr' e3
  return (idHole, IteAnn ann e1
           (holeE2 (getType e2') e2')
           (holeE3 (getType e3') e3'))
nmExpr' const@(ConstAnn ann id args) = do
  normedArgs <- mapM nmExpr' args
  (hole, args') <- nmBinds normedArgs
  return (hole, ConstAnn ann id args')
nmExpr' (TickAnn ann c e) = do
  (hole, e') <- nmExpr' e
  return (hole, TickAnn ann c e')
nmExpr' e = return (idHole, e)

nmMatchArm :: TypedMatchArm -> Norm TypedMatchArm
nmMatchArm (MatchArmAnn ann pat e) = do
  e' <- nmExpr e
  return $ MatchArmAnn ann pat e'

type HoleExpr = Type -> TypedExpr -> TypedExpr

holeCompose :: HoleExpr -> HoleExpr -> HoleExpr
holeCompose h1 h2 = hole 
  where hole t e = h1 t (h2 t e)

srcForBind :: TypedExpr -> ExprSrc
srcForBind e = case (teSrc . getAnn) e of
  (Loc pos) -> DerivedFrom pos
  (DerivedFrom pos) -> DerivedFrom pos


letHole :: TypedExpr -> Id  -> HoleExpr
letHole e v = hole 
  where src = srcForBind e
        hole t = LetAnn (TypedExprAnn src t) v e

idHole :: HoleExpr
idHole = const id

nmBind :: (HoleExpr, TypedExpr) -> Norm (HoleExpr, TypedExpr)
nmBind (holeE, e)
  | isImmediate e = return (idHole, e)
  | otherwise = do
      v <- newVar
      let hole = letHole e v
      let ann = TypedExprAnn src (getType e)
      return (holeE `holeCompose` hole, VarAnn ann v)
        where src = srcForBind e
    

nmBinds :: [(HoleExpr, TypedExpr)] -> Norm (HoleExpr, [TypedExpr])
nmBinds exps = foldM go (idHole, []) =<< mapM nmBind exps
  where go (hole, exps) (hole', exp) = return (hole `holeCompose` hole', exps ++ [exp])

isImmediate :: Expr a -> Bool
isImmediate (Var _) = True
isImmediate _ = False


