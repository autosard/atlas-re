{-# LANGUAGE OverloadedStrings #-}

module Builtin
  ( dataDefs,
    funTypes,
    measures
  ) where

import Syntax (Id)
import Syntax.Types.Scheme
import Syntax.Types.Type
import Syntax.Program

import Data.Map as M
import Syntax.Measure (MeasureEnv (..), ConstPat(..), MeasureAlgebra(..))
import Syntax.ResourceExpression.Size (emptySizeSum)


dataDefs :: DataEnv
dataDefs = M.fromList
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

funTypes :: Map Id Scheme
funTypes = M.fromList
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

measures :: Map Scheme MeasureEnv
measures = M.fromList [
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
