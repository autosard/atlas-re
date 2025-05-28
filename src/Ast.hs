{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

module Ast where

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
import Typing.Type (Type, splitProdType, splitFnType)
import Typing.Subst(Types(apply, tv))
import Typing.Scheme (Scheme, toType)
import Data.Tuple (swap)
import Data.List.Extra (groupSort)
import CostAnalysis.Annotation(BoundFunAnn, BoundAnn)
    
type Fqn = (Text, Text)

printFqn (mod, fn) = T.unpack mod ++ "." ++ T.unpack fn

type Number = Int

data Module a = Module {
  name :: Text,
  modPotentialMap :: Map Type PotentialKind,
  mutRecGroups :: [[Id]],
  defs :: Map Id (FunDef a)
} 

data PotentialKind
  = LogLR
  | LogR
  | LogLRX
  | Polynomial
  | LinLog
  deriving (Eq, Ord, Show)

fns :: Module a -> [FunDef a]
fns = M.elems . defs

modMap :: (FunDef a -> FunDef b) -> Module a -> Module b
modMap f (Module {..}) = Module {defs = M.map f defs, ..} 

modMapM :: Monad m => (FunDef a -> m (FunDef b)) -> Module a -> m (Module b)
modMapM f (Module {..}) = do
  defs' <- mapM f defs 
  return Module {defs = defs', ..}

modReplaceDefs :: Module b -> [FunDef a] -> Module a
modReplaceDefs (Module {..}) newDefs = Module {defs = withIds, ..}
  where fnId (Fn id _ _) = id
        withIds = M.fromList $ zip (map fnId newDefs) newDefs

data FunDef a = FunDef (XFunAnn a) Id [Id] (Expr a)

hasPotential :: FunDef Positioned -> Bool
hasPotential fn = case tfCostAnn (funAnn fn) of
                    Just (Cost True _) -> False
                    Just _ -> True
                    Nothing -> True

data Op = LT | EQ | GT
  deriving (Eq, Show)

data Syntax a
   = SynExpr (Expr a)
   | SynArm (MatchArm a)
   | SynPat (Pattern a)
   | SynPatVar (PatternVar a)

data MatchArm a = MatchArmAnn (XExprAnn a) (Pattern a) (Expr a)

armExpr :: MatchArm a -> Expr a
armExpr (MatchArmAnn _ _ e) = e

data PatternVar a = Id (XExprAnn a) Id
  | WildcardVar (XExprAnn a)

data Pattern a
  = ConstPat (XExprAnn a) Id [PatternVar a]
  | Alias (XExprAnn a) Id
  | WildcardPat (XExprAnn a) 

-- We use extensible AST types to model the different stages (parsed, typed, etc.) (see https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf)

data Expr a
  = VarAnn (XExprAnn a) Id
  | ConstAnn (XExprAnn a) Id [Expr a]
  | IteAnn (XExprAnn a) (Expr a) (Expr a) (Expr a)
  | MatchAnn (XExprAnn a) (Expr a) [MatchArm a]
  | AppAnn (XExprAnn a) Id [Expr a]
  | LetAnn (XExprAnn a) Id (Expr a) (Expr a)
  | TickAnn (XExprAnn a) (Maybe Rational) (Expr a)
  | CoinAnn (XExprAnn a) Rational

type family XExprAnn a
type family XFunAnn a

data CostAnnotation
  = Coeffs BoundFunAnn
  | Cost {worstCase :: Bool, costCoeffs :: BoundAnn}
  deriving (Eq, Show)
  

funAnn :: FunDef a -> XFunAnn a
funAnn (FunDef ann _ _ _) = ann
  
-- pattern synomyms for constructor patterns
pattern PatTreeNode :: XExprAnn a -> PatternVar a -> PatternVar a -> PatternVar a -> Pattern a
pattern PatTreeNode ann l v r <- ConstPat ann "node" [l, v, r]
  where PatTreeNode ann l v r = ConstPat ann "node" [l, v, r]
pattern PatTreeLeaf :: XExprAnn a -> Pattern a
pattern PatTreeLeaf ann <- ConstPat ann "leaf" []
  where PatTreeLeaf ann = ConstPat ann "leaf" []
pattern PatTuple :: XExprAnn a -> PatternVar a -> PatternVar a -> Pattern a
pattern PatTuple ann x y <- ConstPat ann "(,)" [x, y]
  where PatTuple ann x y = ConstPat ann "(,)" [x, y]

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


pattern PatWildcard :: XExprAnn a -> Pattern a
pattern PatWildcard ann <- WildcardPat ann
  where PatWildcard ann = WildcardPat ann
pattern PatAlias :: XExprAnn a -> Id -> Pattern a
pattern PatAlias ann id <- Alias ann id
  where PatAlias ann id = Alias ann id

pattern MatchArm :: Pattern a -> Expr a -> MatchArm a
pattern MatchArm p e <- MatchArmAnn _ p e

pattern Fn :: Id -> [Id] -> Expr a -> FunDef a
pattern Fn id args e <- FunDef _ id args e

containsFn :: Text -> Module a -> Bool
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

printPatVar :: PatternVar a -> String
printPatVar (Id _ id) = T.unpack id
printPatVar (WildcardVar _) = "_"

printPat :: Pattern a -> String
printPat (ConstPat _ id vars) = T.unpack id ++ " " ++(unwords . map printPatVar $ vars)
printPat (Alias _ id) = T.unpack id
printPat (WildcardPat _) = "_"

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

printFuns :: (XExprAnn a -> String) -> Module a -> String
printFuns printExprAnn mod = intercalate "\n\n" (map (printFun printExprAnn) (fns mod)) ++ "\n"

printProg :: Module a -> String
printProg = printFuns (const "")

printProgPositioned :: PositionedModule -> String
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
  mapAnn f (ConstPat ann id vars) = ConstPat (f ann) id (map (mapAnn f) vars)
  mapAnn f (Alias ann id) = Alias (f ann) id
  mapAnn f (WildcardPat ann) = WildcardPat (f ann)

  getAnn (ConstPat ann _ _) = ann
  getAnn (Alias ann _) = ann
  getAnn (WildcardPat ann) = ann

instance Annotated PatternVar a where
  mapAnn f (Id ann id) = Id (f ann) id
  mapAnn f (WildcardVar ann) = WildcardVar (f ann)
  getAnn (Id ann _) = ann
  getAnn (WildcardVar ann) = ann

instance Annotated Syntax a where
  mapAnn f (SynExpr e) = SynExpr $ mapAnn f e
  mapAnn f (SynArm arm) = SynArm $ mapAnn f arm
  mapAnn f (SynPat p) = SynPat $ mapAnn f p
  getAnn (SynExpr e) = getAnn e
  getAnn (SynArm arm) = getAnn arm
  getAnn (SynPat p) = getAnn p

-- parsed
type ParsedSyntax = Syntax Parsed
type ParsedModule = Module Parsed
type ParsedFunDef = FunDef Parsed
type ParsedExpr = Expr Parsed
type ParsedMatchArm = MatchArm Parsed
type ParsedPattern = Pattern Parsed
type ParsedPatternVar = PatternVar Parsed


deriving instance Show ParsedPatternVar
deriving instance Show ParsedPattern
deriving instance Show ParsedMatchArm
deriving instance Show ParsedExpr
deriving instance Show ParsedFunDef

data ParsedFunAnn = ParsedFunAnn {
  pfLoc :: SourcePos,
  pfFqn :: Fqn,
  pfType :: Maybe Scheme,
  pfCostAnn :: Maybe CostAnnotation,
  pfNumCf :: Maybe Int}
  deriving (Eq, Show)

data Parsed
type instance XExprAnn Parsed = SourcePos
type instance XFunAnn Parsed = ParsedFunAnn

pattern FnParsed :: ParsedFunAnn -> Id -> [Id] -> ParsedExpr -> ParsedFunDef
pattern FnParsed ann id args body = FunDef ann id args body


-- typed
type TypedModule = Module Typed
type TypedFunDef = FunDef Typed
type TypedExpr = Expr Typed
type TypedMatchArm = MatchArm Typed
type TypedPattern = Pattern Typed
type TypedPatternVar = PatternVar Typed

deriving instance Show TypedPatternVar
deriving instance Eq TypedPatternVar
deriving instance Show TypedPattern
deriving instance Eq TypedPattern
deriving instance Show TypedMatchArm
deriving instance Eq TypedMatchArm
deriving instance Show TypedExpr
deriving instance Eq TypedExpr
deriving instance Show TypedFunDef

data TypedFunAnn = TypedFunAnn {
  tfLoc :: SourcePos,
  tfFqn :: Fqn,
  tfType :: Scheme,
  tfCostAnn :: Maybe CostAnnotation,
  tfNumCf :: Maybe Int}
  deriving (Eq, Show)

data ExprSrc = Loc SourcePos | DerivedFrom SourcePos
  deriving (Eq, Show)

data TypedExprAnn = TypedExprAnn {
  teSrc :: ExprSrc,
  teType :: Type}
  deriving (Eq, Show)
  
data Typed
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
  
-- getType :: Annotated a Typed => a Typed -> Type
-- getType = teType . getAnn

extendWithType :: Type -> XExprAnn Parsed -> XExprAnn Typed
extendWithType t pos = TypedExprAnn (Loc pos) t

ctxFromFn :: FunDef Positioned -> ([(Id, Type)], [(Id, Type)])
ctxFromFn (FunDef ann _ args _) =
  let (tFrom, tTo) = splitFnType . toType . tfType $ ann
      tsFrom = splitProdType tFrom
      ctxFrom = zip args tsFrom 
      ctxTo = ctxFromType tTo in
    (ctxFrom, ctxTo)
    
ctxFromType :: Type -> [(Id, Type)]
ctxFromType t = let ts = splitProdType t in 
  zip [T.pack $ "e" ++ show n
      |n <- [1..]] ts 

fnArgsByType :: FunDef Positioned -> (Map Type [Id], Map Type [Id])
fnArgsByType fn = let (from, to) = ctxFromFn fn in
                    (toMap from, toMap to)
  where toMap = M.fromList . groupSort . map swap
          --M.fromListWith (++) $ map (\(x, t) -> (t, [x])) args
        

instance Types TypedExpr where
  apply s = mapAnn (\ann -> ann{teType = apply s (teType ann) })
  tv e = tv (getType e)

-- context
type PositionedModule = Module Positioned
type PositionedFunDef = FunDef Positioned
type PositionedExpr = Expr Positioned
type PositionedMatchArm = MatchArm Positioned
type PositionedPattern = Pattern Positioned
type PositionedPatternVar = PatternVar Positioned

deriving instance Show PositionedPatternVar
deriving instance Eq PositionedPatternVar
deriving instance Show PositionedPattern
deriving instance Eq PositionedPattern
deriving instance Show PositionedMatchArm
deriving instance Eq PositionedMatchArm
deriving instance Show PositionedExpr
deriving instance Eq PositionedExpr
deriving instance Show PositionedFunDef
deriving instance Show PositionedModule

data ExprCtx = PseudoLeaf
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

data Positioned
type instance XFunAnn Positioned = TypedFunAnn
type instance XExprAnn Positioned = PositionedExprAnn

extendWithCtx :: Set ExprCtx -> XExprAnn Typed -> XExprAnn Positioned
extendWithCtx ctx (TypedExprAnn {..}) = PositionedExprAnn teSrc teType ctx

data Val = ConstVal !Id ![Val] | NumVal Int
  deriving (Eq)

paren :: String -> String
paren s = "(" ++ s ++ ")"

instance Show Val where
  show (ConstVal id []) = T.unpack id
  show (ConstVal id args) = paren $ T.unpack id ++ " " ++ unwords (map show args)
  show (NumVal n) = show n

printPos :: SourcePos -> String
printPos pos = show (unPos . sourceLine $ pos) ++ ","  ++ show (unPos $ sourceColumn pos)
