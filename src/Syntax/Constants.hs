{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax.Constants where

import Primitive(Id)
import Typing.Scheme
import Typing.Type
import Syntax.Ast

import Data.Map as M
import Syntax.Measure (MeasureEnv (..), ConstPat(..), MeasureAlgebra(..))
import Syntax.ResourceExpression.Size (emptySizeSum)


builtInDataDefs :: DataEnv
builtInDataDefs = M.fromList
  [("()", DataInfo {
       diParams=[],
       diCtors=[
           CtorInfo {
               ciName = "()",
               ciType = Forall 0 (TAp "()" [])
           }]
       }
   ),
   ("(,)", DataInfo {
       diParams=["a","b"],
       diCtors=[
           CtorInfo {
               ciName = "(,)",
               ciType = Forall 2 $
                 TFun (TGen 0) $
                 TFun (TGen 1) $
                 TAp "(,)" [TGen 0, TGen 1]
           }]
       }
   ),
   ("Nat", DataInfo {
       diParams=[],
       diCtors=[
           CtorInfo {
               ciName = "Zero",
               ciType = Forall 0 (TAp "Nat" [])
           },
           CtorInfo {
               ciName = "Suc",
               ciType = Forall 0 (TFun (TAp "Nat" []) (TAp "Nat" []))
           }]
       }
   ),
   ("Bool", DataInfo {
       diParams=[],
       diCtors=[
           CtorInfo {
               ciName = "True",
               ciType = Forall 0 (TAp "Bool" [])
           },
           CtorInfo {
               ciName = "False",
               ciType = Forall 0 (TAp "Bool" [])
           }]
       }
   )]

tNat = TAp "Nat" []

builtInFunTypes :: Map Id Scheme
builtInFunTypes = M.fromList
  [
    ("error", Forall 1 $ [TAp "String" []] `fn` TGen 0)
  , ("+", Forall 0 $ [tNat, tNat] `fn` tNat)
  , ("*", Forall 0 $ [tNat, tNat] `fn` tNat)
  , ("<=", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , (">=", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , ("<", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , (">", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  , ("==", Forall 1 $ [TGen 0, TGen 0] `fn` TAp "Bool" [])
  ]

builtInMeasures :: Map Scheme MeasureEnv
builtInMeasures = M.fromList [
  (Forall 0 (TAp "Bool" []), MeasureEnv {
     sizeMeasure = Equations [
       (ConstPat "True" [], emptySizeSum),
       (ConstPat "False" [], emptySizeSum)
       ]
   , potentialMeasure = Just $ Equations [
       (ConstPat "True" [], []),
       (ConstPat "False" [], [])
       ]
   })
  ]
