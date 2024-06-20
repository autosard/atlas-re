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
testAnnDerived = TypedExprAnn (DerivedFrom sp)

tBool :: Type
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
                      (LetAnn (testAnnDerived tNum) "?:0" (ConstAnn (testAnn tTreeNum) "leaf" [])
                       (LetAnn (testAnnDerived tNum) "?:2" a2'
                        (LetAnn (testAnnDerived tNum) "?:3" a3
                         (AppAnn (testAnn tNum) "testFn" [
                             VarAnn (testAnnDerived tSplay) "?:1",
                             VarAnn (testAnnDerived tTreeNum) "?:2",
                             VarAnn (testAnnDerived tNum) "?:3",
                             VarAnn (testAnn tNum) "x"]))))
        runNorm (nmExpr e) `shouldBe` result
    context "given nested node constructor" $ do
      it "correctly creates a nest let binding" $ do
         let e = ConstAnn (testAnn tTreeNum) "node" [
               VarAnn (testAnn tTreeNum) "al",
               VarAnn (testAnn tNum) "a",
               ConstAnn (testAnn tTreeNum) "node" [
                   VarAnn (testAnn tTreeNum) "ar",
                   VarAnn (testAnn tNum) "b",
                   ConstAnn (testAnn tTreeNum) "node" [
                       VarAnn (testAnn tTreeNum) "br",
                       VarAnn (testAnn tNum) "c",
                       VarAnn (testAnn tTreeNum) "cr"]]]
                 
         let ann = testAnn tTreeNum
         let annNum = testAnn tNum
         let annDeriv = testAnnDerived tTreeNum

         
         let result = LetAnn annDeriv "?:0" (ConstAnn ann "node" [VarAnn ann "br", VarAnn annNum "c", VarAnn ann  "cr"]) (LetAnn annDeriv "?:1" (ConstAnn ann "node" [VarAnn ann "ar", VarAnn annNum "b", VarAnn annDeriv "?:0"]) (ConstAnn ann "node" [VarAnn ann "al", VarAnn annNum "a", VarAnn annDeriv "?:1"]))
         let is = runNorm (nmExpr e)
         is `shouldBe` result 
        
        
    
