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
  | UnboundVariable Id [Id]
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
  show (UnboundVariable x scope) =
    "Unbound variable '" ++ T.unpack x ++ "'. "
    ++ if null scope then "No variables are in scope here."
       else "Variables in scope: " ++ L.intercalate ", " (map T.unpack scope)


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
elabBoundTemplate args e = do
  checkScope args e
  fromResourceExpr <$> elabResourceExpr e

-- | Ensures that a resource or size expression only refers to the given variables.
checkScope :: [Id] -> Expr Parsed -> Elab ()
checkScope scope (VarAnn pos x) = unless (x `elem` scope) $
  throwError $ SourceError pos (UnboundVariable x scope)
checkScope scope (AppAnn _ _ args) = mapM_ (checkScope scope) args
checkScope scope (ConstAnn _ _ args) = mapM_ (checkScope scope) args
checkScope _ _ = return ()


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
           
-- | Compiles the clauses of a function definition into nested matches on the
-- argument variables, following the usual column-wise compilation of pattern
-- matrices. Clauses are tried top to bottom (first-match semantics): a clause
-- whose pattern in the current column is a variable is kept in every
-- constructor branch, and additionally in a final variable branch covering the
-- remaining constructors.
compileClauses :: [Id] -> [SurfaceClause] -> Elab (Expr Elaborated)
compileClauses vars clauses =
  compileRows vars [Row (scArgs c) [] (scBody c) | c <- clauses]

-- | The value a user variable is bound to: a match variable, or a constructor
-- application once the match variable has been destructured.
data Val = VVar Id | VCon Id [Val]

-- | A row of the pattern matrix: the remaining patterns, the user variables
-- bound so far and the body.
data Row = Row [Pattern Parsed] [(Id, Val)] (Expr Parsed)

compileRows :: [Id] -> [Row] -> Elab (Expr Elaborated)
compileRows _ [] = return $
  AppAnn dummyPos "error" [LitAnn dummyPos (LString "no matching clause")]
compileRows [] (Row _ binds body : _) = do
  body' <- elabExpr body
  foldM bindVal body' binds
compileRows (v:vs) rows
  -- variable rule: every row binds the current column to a variable
  | all (isVarLike . rowHead) rows = compileRows vs (map (bindHead v) rows)
  -- constructor rule
  | otherwise = do
      let ctors = L.nub [(c, length ps) | Row (PConst _ c ps : _) _ _ <- rows]
      arms <- forM ctors $ \(c, k) -> do
        fields <- fieldVars c k rows
        let val = VCon c (map VVar fields)
            rows' = map (substRow v val) (concatMap (specialize v c k) rows)
        body <- compileRows (fields ++ vs) rows'
        let pat = PConst dummyPos c (map (PVar dummyPos) fields)
        return $ MatchArmAnn dummyPos pat body
      -- rows with a variable in this column also cover all other constructors
      let varRows = [bindHead v r | r <- rows, isVarLike (rowHead r)]
      defArm <- if null varRows then return [] else do
        y <- freshMatchVar
        body <- compileRows vs (map (substRow v (VVar y)) varRows)
        return [MatchArmAnn dummyPos (PVar dummyPos y) body]
      return $ MatchAnn dummyPos (VarAnn dummyPos v) (arms ++ defArm)
  where
    rowHead (Row (p:_) _ _) = p
    rowHead (Row [] _ _) = error "compileRows: row without patterns"

isVarLike :: Pattern Parsed -> Bool
isVarLike (PVar _ _) = True
isVarLike (PWildcard _) = True
isVarLike _ = False

-- | Removes the first pattern of a row, which must be a variable or wildcard,
-- and records the binding of the variable to the match variable.
bindHead :: Id -> Row -> Row
bindHead v (Row (PVar _ x : ps) binds body) = Row ps ((x, VVar v) : binds) body
bindHead _ (Row (_ : ps) binds body) = Row ps binds body
bindHead _ r = r

-- | The rows of the branch for constructor @c@ with @k@ fields.
specialize :: Id -> Id -> Int -> Row -> [Row]
specialize v c k r@(Row (p : ps) binds body) = case p of
  PConst _ c' qs
    | c' == c   -> [Row (qs ++ ps) binds body]
    | otherwise -> []
  _ -> let Row ps' binds' body' = bindHead v r
       in [Row (replicate k (PWildcard dummyPos) ++ ps') binds' body']
specialize _ _ _ r = [r]

-- | Replaces the match variable @v@ in the bound values, after @v@ has been
-- destructured or rebound by a match.
substRow :: Id -> Val -> Row -> Row
substRow v val (Row ps binds body) = Row ps [(x, go w) | (x, w) <- binds] body
  where go (VVar u) | u == v = val
        go (VVar u) = VVar u
        go (VCon c ws) = VCon c (map go ws)

-- | Variables for the fields of constructor @c@. The name used in the source
-- is kept if it is used consistently at this position and nowhere else in the
-- matrix; otherwise a fresh variable is introduced.
fieldVars :: Id -> Int -> [Row] -> Elab [Id]
fieldVars c k rows = forM [0 .. k - 1] $ \i ->
  case [x | Row (PConst _ c' qs : _) _ _ <- rows, c' == c, PVar _ x <- [qs !! i]] of
    (x : xs) | all (== x) xs && occurrences x == length (x : xs) -> return x
    _ -> freshMatchVar
  where
    occurrences x = length [() | Row ps _ _ <- rows, p <- ps, y <- patVars p, y == x]

patVars :: Pattern Parsed -> [Id]
patVars (PVar _ x) = [x]
patVars (PConst _ _ ps) = concatMap patVars ps
patVars (PWildcard _) = []

-- | Binds a user variable to its value: by a single-armed match for a match
-- variable, or by let-bindings that rebuild a destructured value.
bindVal :: Expr Elaborated -> (Id, Val) -> Elab (Expr Elaborated)
bindVal body (x, VVar v)
  | x == v    = return body
  | otherwise = return $ MatchAnn dummyPos (VarAnn dummyPos v) [MatchArmAnn dummyPos (PVar dummyPos x) body]
bindVal body (x, VCon c ws) = do
  (args, wrap) <- argVars ws
  return $ wrap (LetAnn dummyPos x (ConstAnn dummyPos c (map (VarAnn dummyPos) args)) body)
  where
    -- arguments of a constructor application must be variables (ANF)
    argVars [] = return ([], id)
    argVars (VVar u : rest) = do
      (us, wrap) <- argVars rest
      return (u : us, wrap)
    argVars (VCon c' ws' : rest) = do
      t <- freshMatchVar
      (us, wrap) <- argVars rest
      inner <- bindVal (VarAnn dummyPos t) (t, VCon c' ws')
      let build e = substLet inner e
      return (t : us, build . wrap)
    -- place e as the body of the let-chain that defines t
    substLet (LetAnn a y e1 (VarAnn _ _)) e = LetAnn a y e1 e
    substLet (LetAnn a y e1 rest) e = LetAnn a y e1 (substLet rest e)
    substLet other _ = other

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
  checkScope varNames body
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
