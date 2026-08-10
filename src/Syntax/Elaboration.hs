{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}


module Syntax.Elaboration where

import Data.Map(Map)
import qualified Data.Map as M
import Data.List (singleton)
import Control.Monad.Except
import Control.Monad.State
    ( MonadState(put, get), State, evalState, MonadTrans(lift) )
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Monad
import Text.Megaparsec (SourcePos(SourcePos), pos1)
import Data.Tuple (swap)
import qualified Data.Text as T
import qualified Data.List as L


import Primitive (Id, dbg)
import Syntax.Ast
import Typing.Scheme (Scheme, quantify, quantifyAll)
import Typing.Subst (tv)
import Typing.Type
import Syntax.Measure
import SourceError
import CostAnalysis.Template (BoundTemplate(..))
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size
import StaticAnalysis ( groupFuns )
import Syntax.Constants (builtInMeasures)



newtype ElabState = ElabState {
  idGen :: Int
}

type Elab = ExceptT (SourceError ElabError) (State ElabState)

data ElabError
  = InvalidMeasure
  | ElabError String
  | IllformedResourceTerm String
  | ArgCountMismatch Id Int Int
  deriving Eq

illformedTerm :: Expr Parsed -> String -> Elab a
illformedTerm e msg = throwError $
  SourceError (getAnn e) (IllformedResourceTerm msg)



instance Show ElabError where
  show InvalidMeasure = "Invalid measure definition."
  show (IllformedResourceTerm msg) = msg
  show (ArgCountMismatch name expected found) =
    "Conflicting number of arguments in clauses for function '" ++ T.unpack name ++ "'.\n"
    ++ "  Expected: " ++ show expected ++ "\n"
    ++ "  Found   : " ++ show found
  show (ElabError msg) = msg


freshMatchVar :: Elab Id
freshMatchVar = do
  s <- get
  let n = idGen s
  put s {idGen = n + 1}
  return $ T.pack ("_arg" ++ show n)
  
--------------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------------

elabProgram :: SurfaceProgram -> Either (SourceError ElabError) (Program Elaborated)
elabProgram sp = evalState (runExceptT (elabProg sp)) initState
  
  where initState = ElabState 0

elabProg :: SurfaceProgram -> Elab (Program Elaborated)
elabProg sp = do
  sig <- mapM elabSig (sfSig sp)
  funDefs <- mapM elabFunDef $ sfFunDefs sp
  dataEnv <- elabDataDefs (sfDataDefs sp)
  measureSig <- elabMeasureSig (sfMeasureDefs sp)
  return $ Program {
    _pSig = sig
    , _pConfig = sfConfig sp
    , _pMutRecGroups = groupFuns (M.elems funDefs)
    , _pFunDefs = funDefs
    , _pDataEnv = dataEnv
    , _pMeasureSig = measureSig}

--------------------------------------------------------------------------------
-- Signatures
--------------------------------------------------------------------------------

elabSig :: SurfaceFunSig -> Elab FunSig
elabSig sSig = do
  from <- uncurry elabBoundTemplate (scsFrom sCostSig)
  let (binder, coeffs) = scsTo sCostSig
  to <- elabBoundTemplate [binder] coeffs
  return $ FunSig (sfsType sSig) (Just $ CostSig from to binder)
  where sCostSig = sfsCostSig sSig

elabBoundTemplate :: [Id] -> Expr Parsed -> Elab BoundTemplate
elabBoundTemplate args e = do
  coeffs <- M.fromList <$> elabScalarComb e
  return $ BoundTemplate coeffs

--------------------------------------------------------------------------------
-- Resource Expressions
--------------------------------------------------------------------------------

elabScalarComb :: Expr Parsed -> Elab [(ResourceTerm, Rational)]
elabScalarComb (App "-" [ss, s]) = do
  es <- elabScale s (-1)
  ess <- elabScalarComb ss
  return $ ess ++ [es]
elabScalarComb (App "+" [ss, s]) = do
  es <- elabScale s 1
  ess <- elabScalarComb ss
  return $ ess ++ [es]
elabScalarComb e = singleton <$> elabScale e 1

elabScale :: Expr Parsed -> Rational -> Elab (ResourceTerm, Rational)
elabScale (App "*" [q, t]) sign = do
  qr <- elabRatLit q
  rt <- elabResourceTerm t
  return (rt, sign * qr)
elabScale (Lit (LRat r)) sign = return (RTId, sign * r)
elabScale (Lit (LNat n)) sign = return (RTId, sign * fromIntegral n)
elabScale e sign = do
  rt <- elabResourceTerm e
  return (rt, sign)


elabRatLit :: Expr Parsed -> Elab Rational
elabRatLit (Lit (LRat r)) = return r
elabRatLit (Lit (LNat n)) = return (fromIntegral n)
elabRatLit e = illformedTerm e "Expected a rational number."

elabResourceTerm :: Expr Parsed -> Elab ResourceTerm
elabResourceTerm e = do
  r <- runMaybeT $
    (RTSize <$> elabSizeAtomM e)
    <|> (RTBinoms <$> elabProdTermM e)
    <|> elabLogTermM e
    <|> elabPhiM e
  case r of
    Just r -> pure r
    Nothing -> illformedTerm e "Expected a resource term."

elabPhiM :: Expr Parsed -> MaybeT Elab ResourceTerm
elabPhiM (App "pot" [Var x]) = lift $ return (RTPhi x)
elabPhiM _ = empty

elabLogTermM :: Expr Parsed -> MaybeT Elab ResourceTerm
elabLogTermM (App "log" [s]) = lift $ RTLog <$> elabSizeSum s
elabLogTermM _ = empty
  --illformedTerm e "Expected log term."

elabSizeSum :: Expr Parsed -> Elab SizeSum
elabSizeSum (App "-" [ss, s]) = do
  st <- elabSizeTerm s (-1)
  sts <- elabSizeSum ss
  return $ add st sts 
elabSizeSum (App "+" [ss, s]) = do
  st <- elabSizeTerm s 1
  sts <- elabSizeSum ss
  return $ add st sts 
elabSizeSum e = elabSizeTerm e 1

elabSizeTerm :: Expr Parsed -> Int -> Elab SizeSum
elabSizeTerm (App "size" [Var x]) _ = return $ sizeVar x
elabSizeTerm (Lit (LNat b)) sign = return $ sizeConst (sign * b)
elabSizeTerm (App "*" [k, App "size" [Var x]]) sign = do
  k <- elabIntLit k
  return $ sizeScalar x (sign * k)
elabSizeTerm e _ = illformedTerm e "Expected a size term." 

elabIntLit :: Expr Parsed -> Elab Int
elabIntLit (Lit (LNat n)) = return n 
elabIntLit e = illformedTerm e "Expected a nat literal."
  
elabProdTermM :: Expr Parsed -> MaybeT Elab [(SizeSum, Int)]
elabProdTermM (App "binom" [x,k]) = do
  sx <- lift $ elabSizeSum x
  ck <- lift $ elabIntLit k
  return [(sx,ck)]
elabProdTermM (App "*" [App "binom" [x,k], bs]) = do
  sx <- lift $ elabSizeSum x
  ck <- lift $ elabIntLit k
  ((sx,ck) :) <$> elabProdTermM bs 
elabProdTermM _ = empty

elabSizeAtomM :: Expr Parsed -> MaybeT Elab Id
elabSizeAtomM (App "size" [Var x]) = lift (return x)
elabSizeAtomM _ = empty

-- elabSizeAtom :: Expr Parsed -> Elab SizeTerm
-- elabSizeAtom e = do
--   r <- runMaybeT (elabSizeAtomM e)
--   case r of
--     Just sx -> return sx
--     Nothing ->
--       illformedTerm e "Expected a valid atomic size expression (e.g. 'size x')."

--------------------------------------------------------------------------------
-- Function Clauses
--------------------------------------------------------------------------------

elabFunDef :: SurfaceFunDef -> Elab (FunDef Elaborated)
elabFunDef (SurfaceFunDef name clauses) = do
  put $ ElabState {idGen=0}
  validateClauses name clauses

  case clauses of
    (SurfaceClause pos firstArgs _ : _) -> do
      let numArgs = length firstArgs

      matchVars <- replicateM numArgs freshMatchVar

      bodyExpr <- compileClauses matchVars clauses

      return $ FunDef {
        _funName = name
        , _funArgs = matchVars
        , _funBody = bodyExpr
        }

dummyPos = SourcePos "<elab>" pos1 pos1

elabExpr :: Expr Parsed -> Elab (Expr Elaborated)
elabExpr e = return (mapAnn id e)

elabPattern :: Pattern Parsed -> Pattern Elaborated
elabPattern = mapAnn id
           
compileClauses :: [Id] -> [SurfaceClause] -> Elab (Expr Elaborated)
compileClauses [] [SurfaceClause pos [] body] = elabExpr body
-- compileClauses [] (_:_:_) = throwError $ SourceError (initialPos) (IllformedResourceTerm "Overlapping or redundant clauses.")
compileClauses (v:vs) clauses = do
  -- Group the clauses by their first pattern component
  arms <- mapM (\(SurfaceClause pos (p:ps) body) -> do
                   let p' = elabPattern p
                   body' <- compileClauses vs [SurfaceClause pos ps body]
                   return $ MatchArmAnn (getAnn p') p' body')
                 clauses

  let targetExpr = VarAnn dummyPos v
  return $ MatchAnn dummyPos targetExpr arms
  
validateClauses :: Id -> [SurfaceClause] -> Elab ()
validateClauses name clauses = do
  case clauses of
    [] -> return ()
    (firstClause : rest) -> do
      let expectedCount = length (scArgs firstClause) -- Assuming scArgs gets the Pattern list
      forM_ rest $ \clause -> do
        let foundCount = length (scArgs clause)
        when (expectedCount /= foundCount) $
          throwError $ SourceError (scAnn clause) (ArgCountMismatch name expectedCount foundCount)

--------------------------------------------------------------------------------
-- Data Definitions
--------------------------------------------------------------------------------

elabDataDefs :: [DataDecl] -> Elab DataEnv
elabDataDefs dds = M.fromList <$> mapM elabDataDef dds

elabDataDef :: DataDecl -> Elab (Id, DataInfo)
elabDataDef decl = do
  ctors <- mapM (elabCtorDecl decl) (ddCtors decl)
  return (ddName decl, DataInfo (ddParams decl) ctors)

elabCtorDecl :: DataDecl -> CtorDecl -> Elab CtorInfo
elabCtorDecl dDecl cDecl = do
  let params = map TVar (ddParams dDecl)
  let t = tCurry (ctorArgs cDecl) (TAp (ddName dDecl) params)
  let freeVars = tv t L.\\ ddParams dDecl
  unless (null freeVars) $
    let msg = "Unbound type variable '" ++ T.unpack (head freeVars) ++ "'." in
      throwError $ SourceError (ddPos dDecl) (ElabError msg)
  return $ CtorInfo (ctorName cDecl) (quantify (ddParams dDecl) t)
  
--------------------------------------------------------------------------------
-- Measures
--------------------------------------------------------------------------------

elabAlgebra :: SMeasure m -> [SurfaceClause] -> Elab (MeasureAlgebra m)
elabAlgebra mKind clauses = do
  eqs <- mapM (elabClause mKind) clauses
  return $ Equations eqs

elabClause :: SMeasure m -> SurfaceClause -> Elab (ConstPat, Carrier m)
elabClause mKind (SurfaceClause _ [PConst _ cPat pVars] body) = do
  let varNames = map (\(PVar _ x) -> x) pVars
  terms <- case mKind of
    SSize -> elabSizeSum body
    SPotential -> do
      ts <- elabScalarComb body
      return $ map (uncurry RTScale . swap) ts
  return (ConstPat cPat varNames, terms)    
elabClause _ (SurfaceClause pos _ _) = 
      throwError $ SourceError pos (ElabError "Measure definitions must use constructor patterns.")
      
elabMeasureSig :: [MeasureDef] -> Elab (Map Scheme MeasureEnv)
elabMeasureSig = foldM insertMeasure builtInMeasures
  where
    insertMeasure :: Map Scheme MeasureEnv -> MeasureDef -> Elab (Map Scheme MeasureEnv)
    insertMeasure envMap mDef = do
      -- 1. Generalize the structural type into a Scheme key (e.g., forall a. Tree a)
      let schemeKey = quantifyAll (mType mDef) -- Adjust args to capture free vars if polymorphic
      
      -- 2. Lookup existing env for this data type or create an empty layout
      let existingEnv = M.findWithDefault (MeasureEnv (Equations []) Nothing) schemeKey envMap
      
      -- 3. Update the environment depending on whether it's Size or Potential
      updatedEnv <- case mMeasure mDef of
        Size -> do
          alg <- elabAlgebra SSize (mClauses mDef)
          return $ existingEnv { sizeMeasure = alg }
          
        Potential -> do
          alg <- elabAlgebra SPotential (mClauses mDef)
          return $ existingEnv { potentialMeasure = Just alg }
          
      return $ M.insert schemeKey updatedEnv envMap
  
