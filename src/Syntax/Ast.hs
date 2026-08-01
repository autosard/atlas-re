{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FunctionalDependencies #-}


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
import Data.Tuple (swap)
import Data.List.Extra (groupSort)

import Typing.Type (Type)
import Typing.Subst(Types(apply, tv))
import Typing.Scheme (Scheme)
import Primitive(Id, unionMap, HasVars(..), prettyPrint)
import Syntax.Measure(Measure, MeasureEnv)
import Syntax.ResourceExpression(ResourceTerm)
import CostAnalysis.TemplateLanguage
import CostAnalysis.Template(BoundTemplate)
import Lens.Micro.Platform
    
type Fqn = (Text, Text)

printFqn (mod, fn) = T.unpack mod ++ "." ++ T.unpack fn

type Number = Int

--------------------------------------------------------------------------------
-- Stages
--------------------------------------------------------------------------------

-- We use extensible AST types to model the different stages (parsed, typed, etc.) (see https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf)
data Parsed
data Elaborated
data Typed
data Positioned

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

type family XExprAnn a

data Pattern a
  = PVar (XExprAnn a) Id
  | PConst (XExprAnn a) Id [Pattern a]
  | PWildcard (XExprAnn a)

data Literal
  = LNat Int
  | LRat Rational
  | LString Text
  deriving (Eq, Show)

data MatchArm a = MatchArmAnn (XExprAnn a) (Pattern a) (Expr a)

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

--------------------------------------------------------------------------------
-- Function Definitions & Signatures
--------------------------------------------------------------------------------

data CostSig = CostSig {
  csFrom :: BoundTemplate, 
  csTo :: BoundTemplate,
  csBinder :: Id
} deriving (Eq, Show)


data FunSig = FunSig {
  _typeSig :: Scheme,
  _costSig :: Maybe CostSig
} deriving (Eq, Show)

makeLenses ''FunSig

data FunDef a = FunDef
  { _funName :: Id
  , _funArgs :: [Id]
  , _funBody :: Expr a
  }

makeLenses ''FunDef

--------------------------------------------------------------------------------
-- Core Programs
--------------------------------------------------------------------------------

newtype ProgramConfig = ProgConfig {
  templateConfig :: TemplateLanguageConfig
  }
  deriving (Eq, Show)

type DataEnv = Map Id DataInfo

data DataInfo = DataInfo
  { diParams :: [Id]
  , diCtors  :: [CtorInfo]
  } deriving (Eq, Show)

data CtorInfo = CtorInfo
  { ciName :: Id
  , ciType :: Scheme
  } deriving (Eq, Show)


data Program a = Program {
  _pSig :: Map Id FunSig,
  _pConfig :: ProgramConfig,
  _pMutRecGroups :: [[Id]],
  _pFunDefs :: Map Id (FunDef a),
  _pDataEnv :: DataEnv,
  _pMeasureSig :: Map Scheme MeasureEnv
}

makeLenses ''Program

fns :: Program a -> [FunDef a]
fns = M.elems . _pFunDefs

pMap :: (Expr a -> Expr b) -> Program a -> Program b
pMap f = pFunDefs . traversed . funBody %~ f

pMapFn :: (Id -> Expr a -> Expr b) -> Program a -> Program b
pMapFn f = pFunDefs . traversed %~ mapFun
  where mapFun fun = fun & funBody .~ f (fun ^. funName) (fun ^. funBody)

pMapM :: (Monad m) => (Expr a -> m (Expr b)) -> Program a -> m (Program b)
pMapM = traverseOf (pFunDefs . traversed . funBody)

--------------------------------------------------------------------------------
-- Surface Programs
--------------------------------------------------------------------------------

data SurfaceFunSig = SurfaceFunSig {
  sfsType :: Scheme,
  sfsCostSig :: SurfaceCostSig
} deriving (Eq, Show)

data SurfaceCostSig = SurfaceCostSig {
  scsFrom :: ([Id], Expr Parsed), 
  scsTo :: (Id, Expr Parsed)
} deriving (Eq, Show)


data SurfaceFunDef
  = SurfaceFunDef
      Id
      [SurfaceClause]
  deriving Show
      
data SurfaceClause = SurfaceClause {
  scAnn :: XExprAnn Parsed
  , scArgs :: [Pattern Parsed]
  , scBody :: Expr Parsed
  }
  deriving Show

data SurfaceProgram = SurfaceProgram {
  sfSig :: Map Id SurfaceFunSig,
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
-- Parsed 
--------------------------------------------------------------------------------

deriving instance Show (Pattern Parsed)
deriving instance Eq (Pattern Parsed)

deriving instance Show (MatchArm Parsed)
deriving instance Eq (MatchArm Parsed)

deriving instance Show (Expr Parsed)
deriving instance Eq (Expr Parsed)

deriving instance Show (FunDef Parsed)

newtype ParsedFunAnn = ParsedFunAnn {
  pfLoc :: SourcePos}
  deriving (Eq, Show)

type instance XExprAnn Parsed = SourcePos

--------------------------------------------------------------------------------
-- Elaborated 
--------------------------------------------------------------------------------

data ElaboratedCostSig = ElaboratedCostSig {
  ecsFrom :: ([Id], [(ResourceTerm, Rational)]), 
  ecsTo :: ([Id], [(ResourceTerm, Rational)])
} deriving (Eq, Show)

deriving instance Show (Pattern Elaborated)
deriving instance Show (MatchArm Elaborated)
deriving instance Show (Expr Elaborated)
deriving instance Show (FunDef Elaborated)

type instance XExprAnn Elaborated = SourcePos

--------------------------------------------------------------------------------
-- Typed
--------------------------------------------------------------------------------

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

deriving instance Eq (FunDef Typed)
deriving instance Show (FunDef Typed)

deriving instance Eq (Program Typed)
deriving instance Show (Program Typed)

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

class HasType a where
  type_ :: a -> Type

getType :: (HasType (XExprAnn b), HasAnnotation a b) => a b -> Type
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

instance Types TypedExpr where
  apply s = mapAnn (\ann -> ann{teType = apply s (teType ann) })
  tv e = tv (getType e)

--------------------------------------------------------------------------------
-- Positioned
--------------------------------------------------------------------------------

type PositionedFunDef = FunDef Positioned
type PositionedExpr = Expr Positioned
type PositionedMatchArm = MatchArm Positioned
type PositionedPattern = Pattern Positioned

deriving instance Show (Pattern Positioned)
deriving instance Eq (Pattern Positioned)

deriving instance Show (FunDef Positioned)
deriving instance Eq (FunDef Positioned)

deriving instance Show (Program Positioned)
deriving instance Eq (Program Positioned)

deriving instance Show PositionedMatchArm
deriving instance Eq PositionedMatchArm
deriving instance Show PositionedExpr
deriving instance Eq PositionedExpr


data ExprCtx = PseudoLeaf
  | RecCall 
  | BindsAppOrTick
  | BindsAppOrTickRec
  | FirstAfterApp
  | OutermostLet
  | FirstAfterMatch
  | IteCoin
  deriving (Eq, Ord, Show)

data PositionedExprAnn = PositionedExprAnn {
  peSrc :: ExprSrc,
  peType :: Type,
  peCtx :: Set ExprCtx}
  deriving (Eq, Show)

instance HasType PositionedExprAnn where
  type_ = peType

type instance XExprAnn Positioned = PositionedExprAnn

extendWithCtx :: Set ExprCtx -> XExprAnn Typed -> XExprAnn Positioned
extendWithCtx ctx (TypedExprAnn {..}) = PositionedExprAnn teSrc teType ctx

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

data Syntax a
   = SynExpr (Expr a)
   | SynArm (MatchArm a)
   | SynPat (Pattern a)

armExpr :: MatchArm a -> Expr a
armExpr (MatchArmAnn _ _ e) = e

-- pattern synomyms to work with epxressions without the overhead of annotations
pattern Lit :: Literal -> Expr a
pattern Lit lit <- LitAnn _ lit
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

pattern MatchArm :: Pattern a -> Expr a -> MatchArm a
pattern MatchArm p e <- MatchArmAnn _ p e

containsFn :: Text -> Program a -> Bool
containsFn fn prog = M.member fn (prog^.pFunDefs)

subPatterns :: Pattern a -> [Pattern a]
subPatterns (PVar _ _) = []
subPatterns (PConst _ _ ps) = concatMap subPatterns ps
subPatterns (PWildcard _) = []

instance HasVars (Expr a) where
  freeVars (Var id) = S.singleton id
  freeVars (Const _ exps) = unionMap freeVars exps
  freeVars (Ite e1 e2 e3) = unionMap freeVars [e1, e2, e3]
  freeVars (Match m arms) = freeVars m `S.union`
    unionMap (freeVars . (\(MatchArm _ e) -> e)) arms
  freeVars (App _ exps) = unionMap freeVars exps
  freeVars (Let id e1 e2) = S.delete id $ freeVars e1 `S.union` freeVars e2
  freeVars (Tick _ e) = freeVars e
  freeVars _ = S.empty

printExprHead :: Expr a -> String
printExprHead (Var id) = T.unpack id 
printExprHead (Const id args) = T.unpack id ++ " " ++ unwords (map printExprHead args)
printExprHead (Ite {}) = "ite"
printExprHead (Match (Var id) _) = "match " ++ T.unpack id
printExprHead (App id args) = T.unpack id ++ " " ++ unwords (map printExprHead args)
printExprHead (Let id e1 e2) = "let " ++ T.unpack id ++ " = " ++ printExprHead e1
printExprHead (Tick _ _) = "tick"
printExprHead (Coin _) = "coin"
printExprHead (Lit l) = show l

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
printExpr printAnn _ (LitAnn ann l) = show l ++ printAnn ann
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
  where frac = maybe "" prettyPrint
printExpr printAnn ident (CoinAnn ann p) = "coin " ++ prettyPrint p ++ printAnn ann

printFun :: (XExprAnn a -> String) -> FunDef a -> String
printFun printExprAnn fun = T.unpack (fun^.funName) ++ " " ++ printedArgs ++ " = " ++ printExpr printExprAnn 0 (fun^.funBody)
  where printedArgs = unwords . map T.unpack $ (fun^.funArgs)

printFuns :: (XExprAnn a -> String) -> Program a -> String
printFuns printExprAnn mod = intercalate "\n\n" (map (printFun printExprAnn) (fns mod)) ++ "\n"

printProg :: Program a -> String
printProg = printFuns (const "")

printProgPositioned :: Program Positioned -> String
printProgPositioned = printFuns printCtx
  where printCtx (PositionedExprAnn {..}) = " " ++ paren (intercalate "," (map show (S.toList peCtx)))

class HasAnnotation a b where
  getAnn :: a b -> XExprAnn b
  
class MapAnnotation a b c where
  mapAnn :: (XExprAnn b -> XExprAnn c) -> a b -> a c
  

instance MapAnnotation Expr a b where
  mapAnn f (LitAnn ann lit) = LitAnn (f ann) lit
  mapAnn f (VarAnn ann id) = VarAnn (f ann) id
  mapAnn f (ConstAnn ann id args) = ConstAnn (f ann) id $ map (mapAnn f) args
  mapAnn f (IteAnn ann e1 e2 e3) = IteAnn (f ann) (mapAnn f e1) (mapAnn f e2) (mapAnn f e3)
  mapAnn f (MatchAnn ann e arms) = MatchAnn (f ann) (mapAnn f e) $ map (mapAnn f) arms
  mapAnn f (AppAnn ann id args) = AppAnn (f ann) id $ map (mapAnn f) args
  mapAnn f (LetAnn ann id e1 e2) = LetAnn (f ann) id (mapAnn f e1) (mapAnn f e2)
  mapAnn f (TickAnn ann c e) = TickAnn (f ann) c (mapAnn f e)
  mapAnn f (CoinAnn ann p) = CoinAnn (f ann) p
  
instance HasAnnotation Expr a where
  getAnn (LitAnn ann _) = ann
  getAnn (VarAnn ann _) = ann
  getAnn (ConstAnn ann _ _) = ann
  getAnn (IteAnn ann _ _ _) = ann
  getAnn (MatchAnn ann _ _) = ann
  getAnn (AppAnn ann _ _) = ann
  getAnn (LetAnn ann _ _ _) = ann
  getAnn (TickAnn ann _ _) = ann
  getAnn (CoinAnn ann _) = ann

instance MapAnnotation MatchArm a b where
  mapAnn f (MatchArmAnn ann p e) = MatchArmAnn (f ann) (mapAnn f p) (mapAnn f e)

instance HasAnnotation MatchArm a where  
  getAnn (MatchArmAnn ann _ _) = ann
  

instance MapAnnotation Pattern a b where
  mapAnn f (PConst ann id vars) = PConst (f ann) id (map (mapAnn f) vars)
  mapAnn f (PVar ann id) = PVar (f ann) id
  mapAnn f (PWildcard ann) = PWildcard (f ann)

instance HasAnnotation Pattern a where
  getAnn (PConst ann _ _) = ann
  getAnn (PVar ann _) = ann
  getAnn (PWildcard ann) = ann

instance MapAnnotation Syntax a b where
  mapAnn f (SynExpr e) = SynExpr $ mapAnn f e
  mapAnn f (SynArm arm) = SynArm $ mapAnn f arm
  mapAnn f (SynPat p) = SynPat $ mapAnn f p
  
instance HasAnnotation Syntax a  where
  getAnn (SynExpr e) = getAnn e
  getAnn (SynArm arm) = getAnn arm
  getAnn (SynPat p) = getAnn p

paren :: String -> String
paren s = "(" ++ s ++ ")"

printPos :: SourcePos -> String
printPos pos = show (unPos . sourceLine $ pos) ++ ","  ++ show (unPos $ sourceColumn pos)

toVar :: Expr a -> Maybe Id
toVar (Var x) = Just x
toVar _ = Nothing
