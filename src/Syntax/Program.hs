{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FunctionalDependencies #-}


module Syntax.Program
  ( CostMode (..)
  , ProgramConfig (..)
  , FunDef (..)
  , funName
  , funBody
  , funArgs
  , FunSig (..)
  , typeSig
  , costSig
  , CostSig (..)
  , Program (..)
  , pSig
  , pDataEnv
  , pMeasureSig
  , pFunDefs
  , pMutRecGroups
  , pConfig
  , DataEnv (..)
  , CtorInfo (..)
  , DataInfo (..)
  , pMapM
  , pMapFn
  , fns
  , groupFuns
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Text.Megaparsec(SourcePos)
import Data.List(intercalate)
import Prelude hiding (break)

import Syntax
  (Parsed
  , Typed
  , Elaborated
  , Positioned)
import Syntax.Annotation (XExprAnn)  
import Syntax.Expression (Expr (..), calledFunctions, printExpr)
import Syntax.Types.Type (Type)
import Syntax.Types.Subst(Types(apply, tv))
import Syntax.Types.Scheme (Scheme)
import Syntax (Id, HasVars(..))
import Syntax.PrettyPrint (PrettyPrint (..), prettyPrint)
import Primitive (unionMap)
import Syntax.Measure(Measure, MeasureEnv)
import Syntax.ResourceExpression(ResourceTerm)
import CostAnalysis.TemplateLanguage
import CostAnalysis.Template(BoundTemplate)
import Lens.Micro.Platform
import Data.Graph (stronglyConnComp, SCC(..))


--------------------------------------------------------------------------------
-- Function Definitions & Signatures
--------------------------------------------------------------------------------

data CostSig = CostSig {
  csFrom :: BoundTemplate,
  csArgs :: [Id],
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

data CostMode = Amortized | WorstCase
  deriving (Eq, Show)

data ProgramConfig = ProgConfig {
  templateConfig :: TemplateLanguageConfig,
  analysisModes :: Map Id CostMode
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

pMapFn :: (Id -> Expr a -> Expr b) -> Program a -> Program b
pMapFn f = pFunDefs . traversed %~ mapFun
  where mapFun fun = fun & funBody .~ f (fun ^. funName) (fun ^. funBody)

pMapM :: (Monad m) => (Expr a -> m (Expr b)) -> Program a -> m (Program b)
pMapM = traverseOf (pFunDefs . traversed . funBody)



--------------------------------------------------------------------------------
-- Parsed 
--------------------------------------------------------------------------------

deriving instance Show (FunDef Parsed)

newtype ParsedFunAnn = ParsedFunAnn {
  pfLoc :: SourcePos}
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Elaborated 
--------------------------------------------------------------------------------

data ElaboratedCostSig = ElaboratedCostSig {
  ecsFrom :: ([Id], [(ResourceTerm, Rational)]), 
  ecsTo :: ([Id], [(ResourceTerm, Rational)])
} deriving (Eq, Show)


deriving instance Show (FunDef Elaborated)

--------------------------------------------------------------------------------
-- Typed
--------------------------------------------------------------------------------

deriving instance Eq (FunDef Typed)
deriving instance Show (FunDef Typed)

deriving instance Eq (Program Typed)
deriving instance Show (Program Typed)

data TypedFunAnn = TypedFunAnn {
  tfLoc :: SourcePos,
  tfType :: Scheme}
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Positioned
--------------------------------------------------------------------------------

deriving instance Show (FunDef Positioned)
deriving instance Eq (FunDef Positioned)

deriving instance Show (Program Positioned)
deriving instance Eq (Program Positioned)

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

instance PrettyPrint (Program a) where
  prettyPrint = printFuns (const "")

printFun :: (XExprAnn a -> String) -> FunDef a -> String
printFun printExprAnn fun = T.unpack (fun^.funName) ++ " " ++ printedArgs ++ " = " ++ printExpr printExprAnn 0 (fun^.funBody)
  where printedArgs = unwords . map T.unpack $ (fun^.funArgs)

printFuns :: (XExprAnn a -> String) -> Program a -> String
printFuns printExprAnn mod = intercalate "\n\n" (map (printFun printExprAnn) (fns mod)) ++ "\n"

--------------------------------------------------------------------------------
-- Mutually Recursive Groups
-------------------------------------------------------------------------------

groupFuns :: [FunDef Elaborated] -> [[Id]]
groupFuns defs = map getGroup sccs
  where
    graphEdges = [ (def, _funName def, S.toList $ calledFunctions (def^.funBody)) 
                 | def <- defs 
                 ]
    sccs = stronglyConnComp graphEdges
    getGroup (AcyclicSCC def) = [_funName def]
    getGroup (CyclicSCC defs') = map _funName defs'
