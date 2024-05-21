{-# LANGUAGE OverloadedStrings #-}

module NormalizationSpec where

import Test.Hspec

import Parsing.Program (initialPos)
import Ast
import Normalization
import Typing.Type

sp = initialPos "test.ml"
testAnn :: Type -> TypedExprAnn
testAnn = TypedExprAnn (Loc sp)
testAnnDerived :: Type -> TypedExprAnn
testAnnDerived = TypedExprAnn Derived 

tBool = TAp Bool []
tNum = TAp Num []
tTreeNum = TAp Tree [tNum]
tSplay = [tNum, tTreeNum] `fn` tTreeNum

spec :: Spec
spec = do
  describe "nmExpr" $ do
    context "given an application with non immediate arguments" $ do
      it "binds its non immeditate arguments in let expressions" $ do
        let a1 = AppAnn (testAnn tSplay) "splay" [
              VarAnn (testAnn tNum) "a",
              VarAnn (testAnn tTreeNum) "t"]
        let a2 = ConstAnn (testAnn tTreeNum) "node" [
              VarAnn (testAnn tTreeNum) "l",
              VarAnn (testAnn tNum) "b",
              ConstAnn (testAnn tTreeNum) "leaf" []]
        let a3 = IteAnn (testAnn tNum) (VarAnn (testAnn tBool) "test") (LitAnn (testAnn tNum) (LitNum 2)) (LitAnn (testAnn tNum) (LitNum 3))
        let a4 = VarAnn (testAnn tNum) "x"
        let e = AppAnn (testAnn tNum) "testFn" [a1, a2, a3, a4]
        let a2' = ConstAnn (testAnn tTreeNum) "node" [
              VarAnn (testAnn tTreeNum) "l",
              VarAnn (testAnn tNum) "b",
              VarAnn (testAnnDerived tTreeNum) "?:0"]
        let result = LetAnn
                     (testAnnDerived tNum) "?:1" a1
                      (LetAnn (testAnnDerived tNum) "?:2"
                       (LetAnn (testAnnDerived tTreeNum) "?:0" (ConstAnn (testAnn tTreeNum) "leaf" []) a2')
                        (LetAnn (testAnnDerived tNum) "?:3" a3
                         (AppAnn (testAnn tNum) "testFn" [
                             VarAnn (testAnnDerived tSplay) "?:1",
                             VarAnn (testAnnDerived tTreeNum) "?:2",
                             VarAnn (testAnnDerived tNum) "?:3",
                             VarAnn (testAnn tNum) "x"])))
        runNorm (nmExpr e) `shouldBe` result
        
        
    
