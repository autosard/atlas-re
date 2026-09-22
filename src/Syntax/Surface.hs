{-# LANGUAGE StrictData #-}

module Syntax.Surface
  ( SurfaceCostSig (..)
  , SurfaceFunSig (..)
  , SurfaceClause (..)
  , SurfaceProgram (..)
  , SurfaceFunDef (..)
  , MeasureDef (..)
  , CtorDecl (..)
  , DataDecl (..)
  , SurfaceAxiom (..)
  )where

import Text.Megaparsec (SourcePos)
import Data.Map (Map)

import Syntax (Id, Parsed)
import Syntax.Program (ProgramConfig(..))
import Syntax.Expression
import Syntax.Annotation (XExprAnn)
import Syntax.Pattern 
import Syntax.Measure (Measure)
import Syntax.Types.Scheme
import Syntax.Types.Type 

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
  sfMeasureDefs :: [MeasureDef],
  sfAxioms :: [SurfaceAxiom]
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

data SurfaceAxiom = SurfaceAxiom
  { saPremises :: [Expr Parsed]
  , saConclusion :: Expr Parsed}
  deriving Show
