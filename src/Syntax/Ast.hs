{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

module Syntax.Ast where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Text.Megaparsec(SourcePos, unPos, sourceLine, sourceColumn)
import Data.List(intercalate)
import Prelude hiding (break)

import Primitive(Id, printRat)
import Typing.Type (Type)
import Typing.Subst(Types(apply, tv))
import Typing.Scheme (Scheme, toType)
import Data.Tuple (swap)
import Data.List.Extra (groupSort)
import Syntax.Measure(Measure, MeasureEnv)
import CostAnalysis.TemplateLanguage
import Syntax.ResourceExpression
    
type Fqn = (Text, Text)

printFqn (mod, fn) = T.unpack mod ++ "." ++ T.unpack fn

type Number = Int

data Parsed
data Typed
data Positioned

--------------------------------------------------------------------------------
-- Surface Programs
--------------------------------------------------------------------------------

type TemplateLanguageConfig = [AtomicLang]

newtype ProgramConfig = ProgConfig {
  templateConfig :: TemplateLanguageConfig
  }
  deriving (Show)

type family ProgramSig a

data SurfaceFunDef
  = SurfaceFunDef
      Id
      [SurfaceClause]
  deriving Show
      
data SurfaceClause
  = SurfaceClause
    (XExprAnn Parsed)
    [Pattern Parsed]
    (Expr Parsed)
  deriving Show

data SurfaceProgram = SurfaceProgram {
  sfSig :: Map Id ParsedFunSig,
  sfConfig :: ProgramConfig,
  sfFunDefs :: Map Id SurfaceFunDef,
  sfDataDefs :: [DataDecl],
  sfMeasureDefs :: [MeasureDef]
} deriving Show

data DataDecl = DataDecl {
  ddPos    :: SourcePos,
  ddName   :: Id,
  ddParams :: [Id],     
  ddCtors  :: [CtorDecl]
} deriving Show

data CtorDecl = CtorDecl{
  ctorName :: Id,
  ctorArgs :: [Type]  
} deriving Show

data MeasureDef = MeasureDef {
  mType :: Type,
  mMeasure :: Measure,
  mName :: Id,
  mClauses :: [SurfaceClause]
} deriving Show

--------------------------------------------------------------------------------
-- Core Programs
--------------------------------------------------------------------------------
  
data Program a = Program {
  pSig :: Map Id ParsedFunSig,
  pConfig :: ProgramConfig,
  pMutRecGroups :: [[Id]],
  pFunDefs :: Map Id (FunDef a),
  pDataEnv :: DataEnv,
  pMeasureSig :: Map Scheme MeasureEnv
}

type DataEnv = Map Id DataInfo

data DataInfo = DataInfo
  { diParams :: [Id]
  , diCtors  :: [CtorInfo]
  } deriving Show

data CtorInfo = CtorInfo
  { ciName :: Id
  , ciType :: Scheme
  } deriving Show

data FnConfig = FnConfig {
  costMode :: CostMode,
  numCf :: Maybe Int,
  strongCf :: Bool}
  deriving (Eq, Show)

data PotentialKind
  = LogLR
  | LogR
  | LogL
  | LogLRX
  | Polynomial
  | LinLog
  | LogGolden
  | Rank
  | Weight
  | RightHeavy
  | LogLRXWB
  deriving (Eq, Ord, Show)


fns :: Program a -> [FunDef a]
fns = M.elems . pFunDefs

programMap :: (FunDef a -> FunDef b) -> Program a -> Program b
programMap f (Program {..}) = Program {pFunDefs = M.map f pFunDefs, ..} 

programMapM :: Monad m => (FunDef a -> m (FunDef b)) -> Program a -> m (Program b)
programMapM f (Program {..}) = do
  defs' <- mapM f pFunDefs
  return Program {pFunDefs = defs', ..}

progReplaceDefs :: Program b -> [FunDef a] -> Program a
progReplaceDefs (Program {..}) newDefs = Program {pFunDefs = withIds, ..}
  where fnId (Fn id _ _) = id
        withIds = M.fromList $ zip (map fnId newDefs) newDefs


data FunDef a = FunDef (XFunAnn a) Id [Id] (Expr a)

data CostMode = AmortizedCost | WorstCaseCost | HybridCost
  deriving (Eq, Show)

-- hasPotential :: FunDef Positioned -> [Bool]
-- hasPotential fn = let n = fromMaybe 1 (numSigs (tfFnConfig (funAnn fn))) in
--   case tfCostAnn (funAnn fn) of
--     Just (Cost True _) -> [False]
--     Just (Coeffs target) ->
--       let anns = map to (withCost target) 
--           annsPot = map (any ((not . null) . idxs) . M.elems) anns in
--         if length anns < n
--         then annsPot ++ replicate (n - length anns) True
--         else annsPot
--     Nothing -> replicate n True

data Op = LT | EQ | GT
  deriving (Eq, Show)

data Syntax a
   = SynExpr (Expr a)
   | SynArm (MatchArm a)
   | SynPat (Pattern a)

data MatchArm a = MatchArmAnn (XExprAnn a) (Pattern a) (Expr a)

armExpr :: MatchArm a -> Expr a
armExpr (MatchArmAnn _ _ e) = e
  
data Pattern a
  = PVar (XExprAnn a) Id
  | PConst (XExprAnn a) Id [Pattern a]
  | PWildcard (XExprAnn a)

data Literal
  = LNat Integer
  | LRat Rational
  | LString Text
  deriving (Eq, Show)

-- We use extensible AST types to model the different stages (parsed, typed, etc.) (see https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf)
data Expr a
  = LitAnn (XExprAnn a) Literal
  | VarAnn (XExprAnn a) Id
  | ConstAnn (XExprAnn a) Id [Expr a]
  | IteAnn (XExprAnn a) (Expr a) (Expr a) (Expr a)
  | MatchAnn (XExprAnn a) (Expr a) [MatchArm a]
  | AppAnn (XExprAnn a) Id [Expr a]
  | LetAnn (XExprAnn a) Id (Expr a) (Expr a)
  | TickAnn (XExprAnn a) (Maybe Rational) (Expr a)
  | CoinAnn (XExprAnn a) Rational

type family XExprAnn a
type family XFunAnn a


funAnn :: FunDef a -> XFunAnn a
funAnn (FunDef ann _ _ _) = ann

-- pattern synomyms to work with epxressions without the overhead of annotations
pattern Var :: Id -> Expr a
pattern Var id <- VarAnn _ id
pattern Const :: Id -> [Expr a] -> Expr a
pattern Const id args <- ConstAnn _ id args
pattern Ite :: Expr a -> Expr a -> Expr a -> Expr a
pattern Ite e1 e2 e3 <- IteAnn _ e1 e2 e3
pattern Match :: Expr a -> [MatchArm a] -> Expr a
pattern Match e arms <- MatchAnn _ e arms
pattern App :: Id -> [Expr a] -> Expr a
pattern App id args <- AppAnn _ id args
pattern Let :: Id -> Expr a -> Expr a -> Expr a
pattern Let id e1 e2 <- LetAnn _ id e1 e2
pattern Tick :: Maybe Rational -> Expr a -> Expr a
pattern Tick c e <- TickAnn _ c e
pattern Coin :: Rational -> Expr a
pattern Coin p <- CoinAnn _ p

-- special patterns for constructor expressions
pattern Leaf :: Expr a
pattern Leaf <- ConstAnn _ "leaf" []

pattern Node :: Expr a -> Expr a -> Expr a -> Expr a 
pattern Node l v r <- ConstAnn _ "node" [l, v, r]

pattern Nil :: Expr a
pattern Nil <- ConstAnn _ "nil" []

pattern Cons :: Expr a -> Expr a -> Expr a
pattern Cons x l <- ConstAnn _ "cons" [x, l]

pattern Tuple :: Expr a -> Expr a -> Expr a
pattern Tuple x1 x2 <- ConstAnn _ "(,)" [x1, x2]

pattern Error :: Expr a
pattern Error <- ConstAnn _ "error" []


-- pattern PatWildcard :: XExprAnn a -> Pattern a
-- pattern PatWildcard ann <- WildcardPat ann
--   where PatWildcard ann = WildcardPat ann
-- pattern PatAlias :: XExprAnn a -> Id -> Pattern a
-- pattern PatAlias ann id <- Alias ann id
--   where PatAlias ann id = Alias ann id

pattern MatchArm :: Pattern a -> Expr a -> MatchArm a
pattern MatchArm p e <- MatchArmAnn _ p e

pattern Fn :: Id -> [Id] -> Expr a -> FunDef a
pattern Fn id args e <- FunDef _ id args e

containsFn :: Text -> Program a -> Bool
containsFn fn = any matches . fns
  where matches (FunDef _ id _ _) = id == fn

printExprHead :: Expr a -> String
printExprHead (Var id) = T.unpack id 
printExprHead (Const id args) = T.unpack id ++ " " ++ unwords (map printExprHead args)
printExprHead (Ite {}) = "ite"
printExprHead (Match (Var id) _) = "match " ++ T.unpack id
printExprHead (App id args) = T.unpack id ++ " " ++ unwords (map printExprHead args)
printExprHead (Let id e1 e2) = "let " ++ T.unpack id ++ " = " ++ printExprHead e1
printExprHead (Tick _ _) = "tick"
printExprHead (Coin _) = "coin"

printPat :: Pattern a -> String
printPat (PConst _ id ps) = T.unpack id ++ " " ++(unwords . map printPat $ ps)
printPat (PVar _ id) = T.unpack id
printPat (PWildcard _) = "_"

printMatchArm :: (XExprAnn a -> String) -> Int -> MatchArm a -> String
printMatchArm printAnn ident (MatchArmAnn _ pat e) = "| " ++ printPat pat ++ " -> " ++ printExpr printAnn ident e 

break :: Int -> String
break ident = "\n" ++ replicate (2*ident) ' ' 

printExprPlain :: Expr a -> String
printExprPlain = printExpr (const "") 0 

printExpr :: (XExprAnn a -> String) -> Int -> Expr a -> String
printExpr printAnn _ (VarAnn ann id) = T.unpack id ++ printAnn ann
printExpr printAnn ident (ConstAnn ann "(,)" [x1, x2]) = "(" ++ printExpr printAnn ident x1 ++ ", " ++ printExpr printAnn ident x2 ++ ")" ++ printAnn ann
printExpr printAnn ident (ConstAnn ann id args) = paren $ T.unpack id ++ " " ++ unwords (map (printExpr printAnn ident) args) ++ printAnn ann
printExpr printAnn ident (IteAnn ann e1 e2 e3) = "if " ++ printExpr printAnn ident e1
  ++ printAnn ann 
  ++ break (ident + 1) ++ "then " ++ printExpr printAnn (ident + 1) e2
  ++ break (ident + 1) ++ "else " ++ printExpr printAnn (ident + 1) e3 
printExpr printAnn ident (MatchAnn ann e arms) = "match "
  ++ printExpr printAnn ident e ++ printAnn ann
  ++ break  (ident + 1) ++ printedArms 
  where printedArms = intercalate (break (ident + 1)) . map (printMatchArm printAnn (ident + 1)) $ arms
printExpr printAnn ident (AppAnn ann id args) = paren $ T.unpack id ++ " "
                          ++ (unwords . map (printExpr printAnn ident) $ args) ++ printAnn ann
printExpr printAnn ident (LetAnn ann id e1 e2) = "let " ++ T.unpack id ++ " = " ++ printExpr printAnn ident e1 ++ " in" ++ printAnn ann
                           ++ break (ident + 1) ++ printExpr printAnn (ident + 1) e2
printExpr printAnn ident (TickAnn ann c e) = "~" ++  frac c ++ printExpr printAnn ident e ++ printAnn ann
  where frac = maybe "" printRat 
printExpr printAnn ident (CoinAnn ann p) = "coin " ++ printRat p ++ printAnn ann

printFun :: (XExprAnn a -> String) -> FunDef a -> String
printFun printExprAnn (Fn id args body) = T.unpack id ++ " " ++ printedArgs ++ " = " ++ printExpr printExprAnn 0 body
  where printedArgs = unwords . map T.unpack $ args

printFuns :: (XExprAnn a -> String) -> Program a -> String
printFuns printExprAnn mod = intercalate "\n\n" (map (printFun printExprAnn) (fns mod)) ++ "\n"

printProg :: Program a -> String
printProg = printFuns (const "")

printProgPositioned :: PositionedProgram -> String
printProgPositioned = printFuns printCtx
  where printCtx (PositionedExprAnn {..}) = " " ++ paren (intercalate "," (map show (S.toList peCtx)))

class Annotated a b where
  getAnn :: a b -> XExprAnn b
  mapAnn :: (XExprAnn b -> XExprAnn b) -> a b -> a b

instance Annotated Expr a where
  mapAnn f (VarAnn ann id) = VarAnn (f ann) id
  mapAnn f (ConstAnn ann id args) = ConstAnn (f ann) id $ map (mapAnn f) args
  mapAnn f (IteAnn ann e1 e2 e3) = IteAnn (f ann) (mapAnn f e1) (mapAnn f e2) (mapAnn f e3)
  mapAnn f (MatchAnn ann e arms) = MatchAnn (f ann) (mapAnn f e) $ map (mapAnn f) arms
  mapAnn f (AppAnn ann id args) = AppAnn (f ann) id $ map (mapAnn f) args
  mapAnn f (LetAnn ann id e1 e2) = LetAnn (f ann) id (mapAnn f e1) (mapAnn f e2)
  mapAnn f (TickAnn ann c e) = TickAnn (f ann) c (mapAnn f e)
  mapAnn f (CoinAnn ann p) = CoinAnn (f ann) p

  getAnn (VarAnn ann _) = ann
  getAnn (ConstAnn ann _ _) = ann
  getAnn (IteAnn ann _ _ _) = ann
  getAnn (MatchAnn ann _ _) = ann
  getAnn (AppAnn ann _ _) = ann
  getAnn (LetAnn ann _ _ _) = ann
  getAnn (TickAnn ann _ _) = ann
  getAnn (CoinAnn ann _) = ann

instance Annotated MatchArm a where
  mapAnn f (MatchArmAnn ann p e) = MatchArmAnn (f ann) (mapAnn f p) (mapAnn f e)
  getAnn (MatchArmAnn ann _ _) = ann
  

instance Annotated Pattern a where
  mapAnn f (PConst ann id vars) = PConst (f ann) id (map (mapAnn f) vars)
  mapAnn f (PVar ann id) = PVar (f ann) id
  mapAnn f (PWildcard ann) = PWildcard (f ann)

  getAnn (PConst ann _ _) = ann
  getAnn (PVar ann _) = ann
  getAnn (PWildcard ann) = ann

instance Annotated Syntax a where
  mapAnn f (SynExpr e) = SynExpr $ mapAnn f e
  mapAnn f (SynArm arm) = SynArm $ mapAnn f arm
  mapAnn f (SynPat p) = SynPat $ mapAnn f p
  getAnn (SynExpr e) = getAnn e
  getAnn (SynArm arm) = getAnn arm
  getAnn (SynPat p) = getAnn p

--------------------------------------------------------------------------------
-- Parsed Programs
--------------------------------------------------------------------------------

data ParsedCostSig = ParsedCostSig {
  pcsFrom :: ([Id], ParsedExpr), 
  pcsTo :: ([Id], ParsedExpr)
} deriving Show

data ParsedFunSig = ParsedFunSig {
  typeSig :: Scheme,
  costSig :: ParsedCostSig
} deriving Show

type ParsedSyntax = Syntax Parsed
type ParsedProgram = Program Parsed
type ParsedFunDef = FunDef Parsed
type ParsedExpr = Expr Parsed
type ParsedMatchArm = MatchArm Parsed
type ParsedPattern = Pattern Parsed

deriving instance Show ParsedPattern
deriving instance Show ParsedMatchArm
deriving instance Show ParsedExpr
deriving instance Show ParsedFunDef

newtype ParsedFunAnn = ParsedFunAnn {
  pfLoc :: SourcePos}
  deriving (Eq, Show)


type instance XExprAnn Parsed = SourcePos
type instance XFunAnn Parsed = ParsedFunAnn

pattern FnParsed :: ParsedFunAnn -> Id -> [Id] -> ParsedExpr -> ParsedFunDef
pattern FnParsed ann id args body = FunDef ann id args body


-- typed
type TypedProgram = Program Typed
type TypedFunDef = FunDef Typed
type TypedExpr = Expr Typed
type TypedMatchArm = MatchArm Typed
type TypedPattern = Pattern Typed

deriving instance Show TypedPattern
deriving instance Eq TypedPattern
deriving instance Show TypedMatchArm
deriving instance Eq TypedMatchArm
deriving instance Show TypedExpr
deriving instance Eq TypedExpr
deriving instance Show TypedFunDef

data TypedFunAnn = TypedFunAnn {
  tfLoc :: SourcePos,
  tfType :: Scheme}
  deriving (Eq, Show)

data ExprSrc = Loc SourcePos | DerivedFrom SourcePos
  deriving (Eq, Show)

data TypedExprAnn = TypedExprAnn {
  teSrc :: ExprSrc,
  teType :: Type}
  deriving (Eq, Show)
  

type instance XExprAnn Typed = TypedExprAnn
type instance XFunAnn Typed = TypedFunAnn

class HasType a where
  type_ :: a -> Type

getType :: (HasType (XExprAnn b), Annotated a b) => a b -> Type
getType = type_ . getAnn

varWithType :: (HasType (XExprAnn a)) => Expr a -> (Id, Type)
varWithType e@(Var id) = (id, getType e)
varWithType _ = error "varWithType called for non-variable expression."

varsByType :: HasType (XExprAnn a) => [Expr a] -> Map Type [Id]
varsByType es = M.fromList . groupSort $ map (swap . varWithType) es

instance HasType TypedExprAnn where
  type_ = teType

extendWithType :: Type -> XExprAnn Parsed -> XExprAnn Typed
extendWithType t pos = TypedExprAnn (Loc pos) t

-- ctxFromFn :: FunDef Positioned -> ([(Id, Type)], [(Id, Type)])
-- ctxFromFn (FunDef ann _ args _) =
--   let (tFrom, tTo) = splitFnType . toType . tfType $ ann
--       tsFrom = splitProdType tFrom
--       ctxFrom = zip args tsFrom 
--       ctxTo = ctxFromType tTo in
--     (ctxFrom, ctxTo)

    
-- ctxFromType :: Type -> [(Id, Type)]
-- ctxFromType t = let ts = splitProdType t in 
--   zip [T.pack $ "e" ++ show n
--       |n <- [1..]] ts 

-- returnTypeToArgs :: Type -> [Id]
-- returnTypeToArgs t = map fst (ctxFromType t)


-- fnArgsByType :: FunDef Positioned -> (Map Type [Id], Map Type [Id])
-- fnArgsByType fn = let (from, to) = ctxFromFn fn in
--                     (toMap from, toMap to)
--   where toMap = M.fromList . groupSort . map swap
--           --M.fromListWith (++) $ map (\(x, t) -> (t, [x])) args
        

instance Types TypedExpr where
  apply s = mapAnn (\ann -> ann{teType = apply s (teType ann) })
  tv e = tv (getType e)

-- context
type PositionedProgram = Program Positioned
type PositionedFunDef = FunDef Positioned
type PositionedExpr = Expr Positioned
type PositionedMatchArm = MatchArm Positioned
type PositionedPattern = Pattern Positioned

deriving instance Show PositionedPattern
deriving instance Eq PositionedPattern
deriving instance Show PositionedMatchArm
deriving instance Eq PositionedMatchArm
deriving instance Show PositionedExpr
deriving instance Eq PositionedExpr
deriving instance Show PositionedFunDef
deriving instance Show PositionedProgram

data ExprCtx = PseudoLeaf
  | RecCall 
  | BindsAppOrTick
  | BindsAppOrTickRec
  | FirstAfterApp
  | OutermostLet
  | FirstAfterMatch
  | IteCoin
  | ConstEmptyTree
  deriving (Eq, Ord, Show)

data PositionedExprAnn = PositionedExprAnn {
  peSrc :: ExprSrc,
  peType :: Type,
  peCtx :: Set ExprCtx}
  deriving (Eq, Show)

instance HasType PositionedExprAnn where
  type_ = peType


type instance XFunAnn Positioned = TypedFunAnn
type instance XExprAnn Positioned = PositionedExprAnn

extendWithCtx :: Set ExprCtx -> XExprAnn Typed -> XExprAnn Positioned
extendWithCtx ctx (TypedExprAnn {..}) = PositionedExprAnn teSrc teType ctx

-- data Val = ConstVal !Id ![Val] | NumVal Int
--   deriving (Eq)

paren :: String -> String
paren s = "(" ++ s ++ ")"

-- instance Show Val where
--   show (ConstVal id []) = T.unpack id
--   show (ConstVal id args) = paren $ T.unpack id ++ " " ++ unwords (map show args)
--   show (NumVal n) = show n

printPos :: SourcePos -> String
printPos pos = show (unPos . sourceLine $ pos) ++ ","  ++ show (unPos $ sourceColumn pos)

toVar :: Expr a -> Maybe Id
toVar (Var x) = Just x
toVar _ = Nothing



