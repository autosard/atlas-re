{-# LANGUAGE OverloadedStrings #-}

module EvalSpec(spec) where

import Test.Hspec
import qualified Data.Map as M

import Ast
import System.Random
import Parsing.Program (initialPos)
import Constants (boolT, boolSc)
import Eval
import Data.Ratio ( (%) )

testRng = mkStdGen 42
testState = EvalState testRng 0
testDefinitions = M.empty
testEval = evalEval testDefinitions testState
testAnn = TypedExprAnn (Loc (initialPos "test.ml")) boolT

spec = do
  describe "evalExpr" $ do
    context "for a variable" $ do
      it "returns the value from the environment" $ do
        let val = NumVal 3
        let env = M.fromList [("x", val)]
        let e = VarAnn testAnn "x"
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, val)
    context "for a literal" $ do
      it "returns a literal value" $ do
        let val = NumVal 3
        let env = M.empty
        let e = ConstAnn testAnn "num#3" []
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, val)
    context "for a constant" $ do
      it "returns a constant value" $ do
        let xVal = ConstVal "leaf" []
        let val = ConstVal "node" [ConstVal "leaf" [], NumVal 3, ConstVal "leaf" []]
        let env = M.fromList [("x", xVal)]
        let e = ConstAnn testAnn "node" [VarAnn testAnn "x", ConstAnn testAnn "num#3" [], ConstAnn testAnn "leaf" []]
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, val)
    context "for a ite" $ do
      it "returns the correct branch value" $ do
        let v1 = NumVal 1
        let v2 = NumVal 2
        let test = ConstVal "false" []
        let env = M.fromList [("x", test)]
        let e = IteAnn testAnn (VarAnn testAnn "x") (ConstAnn testAnn "num#1" []) (ConstAnn testAnn "num#2" [])
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, v2)
    context "for a match" $ do
      it "returns the value from the matching arm" $ do
        let v = NumVal 3
        let matched = ConstVal "node" [ConstVal "leaf" [], NumVal 3, ConstVal "leaf" []]
        let env = M.fromList [("matched", matched), ("x", v)]
        let arm1 = MatchArmAnn testAnn (PatTreeLeaf testAnn) (VarAnn testAnn "arm1")
        let arm2 = MatchArmAnn testAnn (PatTreeNode testAnn (Id testAnn "l") (Id testAnn "v") (Id testAnn "r")) (VarAnn testAnn "v")
        let e = MatchAnn testAnn (VarAnn testAnn "matched") [arm1, arm2]
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, v)
    context "for a function application" $ do
      it "returns the value of the function body considering the bound arguments" $ do
        let v = NumVal 3
        let env = M.fromList [("x", v)]
        let funAnn = TypedFunAnn (initialPos "test.ml") ("test", "id") boolSc Nothing Nothing
        let defs = M.fromList [("id", FunDef funAnn "id" ["x"] (VarAnn testAnn "x"))]
        let e = AppAnn testAnn "id" [VarAnn testAnn "x"] 
        let r = evalEval defs testState $ evalExpr env e
        r `shouldBe` Right (0, v)
    context "for a let expression" $ do
      it "correctly binds the outer expression" $ do
        let env = M.empty
        let v = NumVal 3
        let e1 = ConstAnn testAnn "num#3" []
        let e2 = VarAnn testAnn "x"
        let e = LetAnn testAnn "x" e1 e2
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, v)
    context "for a coin expression" $ do
      it "returns a random bool" $ do
        let env = M.empty
        let v = ConstVal "false" []
        let e = CoinAnn testAnn (1%2)
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (0, v)
    context "for a tick expression" $ do
      it "adds cost" $ do
        let val = NumVal 3
        let env = M.fromList [("x", val)]
        let e = TickAnn testAnn (Just 2) (VarAnn testAnn "x")
        let r = testEval $ evalExpr env e
        r `shouldBe` Right (2, val)
        
 
    
        

        
        
        
