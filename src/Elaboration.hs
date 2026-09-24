{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}


module Elaboration (elabProgram) where

import Data.Map(Map)
import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad.State
    ( MonadState(put, get), State, evalState, MonadTrans(lift) )
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Monad
import Text.Megaparsec (SourcePos(SourcePos), pos1)
import qualified Data.Text as T
import qualified Data.List as L
import Data.Maybe(mapMaybe)


import Syntax (Id, Parsed, Elaborated)
import Syntax.Surface
import Syntax.Program
import Syntax.Expression
import Syntax.Pattern
import Syntax.Annotation (mapAnn, getAnn)
import Syntax.Types.Scheme (Scheme, quantify, quantifyAll, tFunArgs)
import Syntax.Types.Subst (tv)
import Syntax.Types.Type
import Syntax.Measure
import SourceError
import CostAnalysis.Template (BoundTemplate(..), fromResourceExpr)
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Pattern
import qualified Builtin (measures, dataDefs)
import Syntax.FreeModule (FreeModule)
import qualified Syntax.FreeModule as FM
import Syntax.ResourceExpression.Axioms (AxiomSpec (..))


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
  parsedDataEnv <- elabDataDefs (sfDataDefs sp)
  let dataEnv = M.union Builtin.dataDefs parsedDataEnv
  measureSig <- elabMeasureSig (sfMeasureDefs sp)
  axioms <- mapM elabAxiom $ sfAxioms sp
  return $ Program {
    _pSig = sig
    , _pConfig = sfConfig sp
    , _pMutRecGroups = groupFuns (M.elems funDefs)
    , _pFunDefs = funDefs
    , _pDataEnv = dataEnv
    , _pMeasureSig = measureSig
    , _pAxioms = axioms}

--------------------------------------------------------------------------------
-- Signatures
--------------------------------------------------------------------------------

elabSig :: SurfaceFunSig -> Elab FunSig
elabSig sSig = do
  from <- uncurry elabBoundTemplate (scsFrom sCostSig)
  let fromArgs = fst (scsFrom sCostSig)
  let argTypes = tFunArgs (sfsType sSig)
  let rFromArgs = mapMaybe (\(x, t) -> if isResourceRelevant t then Just x else Nothing)
        $ zip fromArgs argTypes
    
  let (binder, coeffs) = scsTo sCostSig
  to <- elabBoundTemplate [binder] coeffs
  return $ FunSig (sfsType sSig) (Just $ CostSig from rFromArgs to binder)
  where sCostSig = sfsCostSig sSig

elabBoundTemplate :: [Id] -> Expr Parsed -> Elab BoundTemplate
elabBoundTemplate args e = fromResourceExpr <$> elabResourceExpr e


--------------------------------------------------------------------------------
-- Resource Expressions / Patterns
--------------------------------------------------------------------------------

elabRatLit :: Expr Parsed -> Elab Rational
elabRatLit (Lit (LRat r)) = return r
elabRatLit (Lit (LNat n)) = return (fromIntegral n)
elabRatLit e = illformedTerm e "Expected a rational number."

elabFreeModule :: (Ord a) => (Expr Parsed -> Elab (FreeModule a Rational)) -> Expr Parsed -> Elab (FreeModule a Rational)
elabFreeModule  elabAtom (App "-" [ss, s]) = do
  es <- FM.scale (-1) <$> elabAtom s
  ess <- elabFreeModule  elabAtom ss
  return $ FM.add es ess
elabFreeModule elabAtom  (App "+" [ss, s]) = do
  es <- elabAtom s
  ess <- elabFreeModule elabAtom ss 
  return $ FM.add es ess
elabFreeModule elabAtom e = elabAtom e

elabProd :: (Monoid a, Ord a) => (Expr Parsed -> Elab a) -> Expr Parsed -> Elab (FreeModule a Rational)
elabProd _ (Lit (LRat r)) = return $ FM.singleton' mempty r
elabProd _ (Lit (LNat n)) = return $ FM.singleton' mempty (fromIntegral n)
elabProd elabAtom (App "*" [q@(Lit _), t]) = do
  qr <- elabRatLit q
  p <- elabProd elabAtom t
  return $ FM.scale qr p
elabProd elabAtom (App "*" [t, q@(Lit _)]) = do
  qr <- elabRatLit q
  p <- elabProd elabAtom t
  return $ FM.scale qr p
elabProd elabAtom (App "*" [x, y]) = do
  p1 <- elabProd elabAtom x
  p2 <- elabProd elabAtom y
  return (FM.mult p1 p2)
elabProd elabAtom e = FM.singleton <$> elabAtom e

--------------------------------------------------------------------------------
-- Resource Terms
--------------------------------------------------------------------------------

elabResourceExpr :: Expr Parsed -> Elab (FreeModule ResourceTerm Rational)
elabResourceExpr = elabFreeModule (elabProd elabResourceTerm)

elabResourceTerm :: Expr Parsed -> Elab ResourceTerm
elabResourceTerm e = do
  r <- runMaybeT $
    (RTSize <$> elabSizeAtomM e)
    <|> elabLogTermM e
    <|> elabPhiM e
    <|> elabBinom e
  case r of
    Just r -> pure r
    Nothing -> illformedTerm e "Expected a resource term."

elabPhiM :: Expr Parsed -> MaybeT Elab ResourceTerm
elabPhiM (App "pot" [Var x]) = lift $ return (RTPhi x)
elabPhiM _ = empty

elabLogTermM :: Expr Parsed -> MaybeT Elab ResourceTerm
elabLogTermM (App "log" [s]) = lift $ RTLog <$> elabSizeExpr s
elabLogTermM _ = empty

elabSizeExpr :: Expr Parsed -> Elab SizeExpr
elabSizeExpr = elabFreeModule elabSizeTerm

elabSizeTerm :: Expr Parsed -> Elab SizeExpr
elabSizeTerm (App "size" [Var x]) = return $ FM.singleton (SVar x)
elabSizeTerm (Lit (LNat b)) = return $ FM.singleton' SId (fromIntegral b)
elabSizeTerm e = illformedTerm e "Expected a size term." 

elabIntLit :: Expr Parsed -> Elab Int
elabIntLit (Lit (LNat n)) = return n 
elabIntLit e = illformedTerm e "Expected a nat literal."

elabBinom :: Expr Parsed -> MaybeT Elab ResourceTerm
elabBinom (App "binom" [x,k]) = do
  sx <- lift $ elabSizeExpr x
  ck <- lift $ elabIntLit k
  return $ RTBinom sx ck
elabBinom _ = empty  

elabSizeAtomM :: Expr Parsed -> MaybeT Elab Id
elabSizeAtomM (App "size" [Var x]) = lift (return x)
elabSizeAtomM _ = empty

--------------------------------------------------------------------------------
-- Resource Patterns
--------------------------------------------------------------------------------

elabResourcePattern :: Expr Parsed -> Elab ResourcePattern
elabResourcePattern = elabFreeModule (elabProd elabTermPattern)

elabTermPattern :: Expr Parsed -> Elab TermPattern
elabTermPattern e = do 
  r <- runMaybeT $
    (TPVar <$> elabPatVarM e)
    <|> elabLogPatternM e
    <|> elabPhiPatternM e
    <|> elabBinomPattern e
  case r of
    Just r -> pure r
    Nothing -> illformedTerm e "Expected a resource pattern."

elabLogPatternM :: Expr Parsed -> MaybeT Elab TermPattern
elabLogPatternM (App "log" [s]) = lift $ TPLog <$> elabSizePattern s
elabLogPatternM _ = empty

elabPhiPatternM :: Expr Parsed -> MaybeT Elab TermPattern
elabPhiPatternM (App "pot" [Var x]) = lift $ return (TPPhi x)
elabPhiPatternM _ = empty

elabBinomPattern :: Expr Parsed -> MaybeT Elab TermPattern
elabBinomPattern (App "binom" [x,k]) = do
  sx <- lift $ elabSizePattern x
  ck <- lift $ elabIntLit k
  return $ TPBinom sx ck
elabBinomPattern _ = empty

elabPatVarM :: Expr Parsed -> MaybeT Elab Id
elabPatVarM (Var x) = lift (return x)
elabPatVarM _ = empty

elabSizePattern :: Expr Parsed -> Elab SizePattern
elabSizePattern = elabFreeModule elabSizeTermPattern

elabSizeTermPattern :: Expr Parsed -> Elab SizePattern
elabSizeTermPattern (Var x) = return $ FM.singleton (SPVar x)
elabSizeTermPattern (Lit (LNat b)) = return $ FM.singleton SPId
elabSizeTermPattern e = illformedTerm e "Expected a size term pattern." 

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
    SSize -> elabSizeExpr body
    SPotential -> do
      ts <- elabResourceExpr body
      return $ M.map RSConst ts
      
  return (ConstPat cPat varNames, terms)    
elabClause _ (SurfaceClause pos _ _) = 
      throwError $ SourceError pos (ElabError "Measure definitions must use constructor patterns.")
      
elabMeasureSig :: [MeasureDef] -> Elab (Map Scheme MeasureEnv)
elabMeasureSig = foldM insertMeasure Builtin.measures
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
  
--------------------------------------------------------------------------------
-- Axioms
--------------------------------------------------------------------------------

elabResourceIneq :: Expr Parsed -> Elab IneqPattern
elabResourceIneq (App "<=" [lhs, rhs]) = do
  lhsPat <- elabResourcePattern lhs
  rhsPat <- elabResourcePattern rhs
  return $ LeZero (FM.add lhsPat (FM.scale (-1) rhsPat))
elabResourceIneq (App ">=" [lhs, rhs]) = do
  lhsPat <- elabResourcePattern lhs
  rhsPat <- elabResourcePattern rhs
  return $ LeZero (FM.add (FM.scale (-1) lhsPat) rhsPat)
elabResourceIneq e = illformedTerm e "Expected an inequality."

elabAxiom :: SurfaceAxiom -> Elab AxiomSpec
elabAxiom sa = do
  premises <- mapM elabResourceIneq (saPremises sa)
  conclusion <- elabResourceIneq (saConclusion sa)
  return $ AxiomSpec premises conclusion
