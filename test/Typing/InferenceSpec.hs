{-# LANGUAGE OverloadedStrings #-}

module Typing.InferenceSpec(spec) where

import Test.Hspec

import Typing.Inference
import Ast
import Typing.Type
import Typing.Scheme
import Typing.Subst
import qualified Data.Map as M
import Data.Void
import Parsing.Program (initialPos)
import Data.Maybe(fromMaybe)
import Data.Bifunctor(bimap)
import Data.Ratio((%))

tBool = TAp Bool []
tNum = TAp Num []
tTreeNum = TAp Tree [tNum]

isTreeType (TAp Tree _) = True
isTreeType _ = False

testState = TiState 0 nullSubst []
sp = initialPos "test.ml"
pfann = ParsedFunAnn sp ("", "") Nothing Nothing

spec :: Spec
spec = do
  describe "tiExpr" $ do
    context "for a variable expression" $ do
      it "finds its type in the provided context" $ do
        let ctx = M.fromList [("a", toScheme tBool)]
        let e = VarAnn sp "a"
        let e' = evalTI testState (tiExpr ctx e)
        getType <$> e' `shouldBe` Right tBool
      it "throws UnboundIdentifier when the variable is not in the context" $ do
        let ctx = M.empty
        let e = VarAnn sp "a"
        let r = evalTI testState (tiExpr ctx e)
        r `shouldBe` Left (UnboundIdentifier "a")
        
    context "given a number literal expression" $ do
      it "returns a number type" $ do
        let ctx = M.empty
        let e = LitAnn sp (LitNum 13)
        let e' = evalTI testState (tiExpr ctx e)
        getType <$> e' `shouldBe` Right tNum
        
    context "given a ite expression" $ do
      it "returns the correct type" $ do
        let ctx = M.fromList [("cond", toScheme tBool), ("a", toScheme tTreeNum), ("b", toScheme tTreeNum)]
        let e = IteAnn sp (VarAnn sp "cond") (VarAnn sp "a") (VarAnn sp "b")
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s . getType <$> e' `shouldBe` Right tTreeNum
        
    context "for ite with non boolean condition" $ do
      it "throws TypeMismatch" $ do
        let ctx = M.fromList [("cond", toScheme tNum), ("a", toScheme tTreeNum), ("b", toScheme tTreeNum)]
        let e = IteAnn sp (VarAnn sp "cond") (VarAnn sp "a") (VarAnn sp "b")
        let e' = evalTI testState (tiExpr ctx e)
        getType <$> e' `shouldBe` Left (TypeMismatch tBool tNum)
        
    context "given a valid match expression" $ do
      it "returns the correct type" $ do
        let ctx = M.fromList [("t", toScheme (TVar $ Tyvar "t")), ("arm1", toScheme tNum), ("arm2", toScheme tNum)]
        let arm1 = MatchArmAnn sp (PatTreeLeaf sp) (VarAnn sp "arm1")
        let arm2 = MatchArmAnn sp (PatTreeNode sp (Id sp "l") (Id sp "v") (Id sp "r")) (VarAnn sp "arm2")
        let e = MatchAnn sp (VarAnn sp "t") [arm1, arm2]
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s . getType <$> e' `shouldBe` Right tNum
        
    context "given a valid application expression with untyped function" $ do
      it "returns polymorphic type" $ do
        let to = tTreeNum
        let ctx = M.fromList [("a", toScheme tNum), ("t", toScheme tTreeNum), ("splay", toScheme (TVar $ Tyvar "splay"))]
        let e = AppAnn sp "splay" [VarAnn sp "a", VarAnn sp "t"]
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state
        let isCorrect (TVar _) = True
            isCorrect _ = False
        apply s .getType <$> e' `shouldSatisfy` either (const False) isCorrect
        
    context "given a valid application expreson with typed function" $ do
      it "returns monomorphic type" $ do
        let to = tTreeNum
        let ctx = M.fromList [("a", toScheme tNum), ("t", toScheme tTreeNum), ("splay", toScheme ([tNum, tTreeNum] `fn` tTreeNum))]
        let e = AppAnn sp "splay" [VarAnn sp "a", VarAnn sp "t"]
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s . getType <$> e' `shouldBe` Right to
        
    -- context "A boolean expression" $ do
    --   it "returns a bool type" $ do
    --     let ctx = M.fromList [("a", toScheme tNum), ("b", toScheme tNum)]
    --     let e = BExprAnn sp Ast.LT (VarAnn sp "a") (VarAnn sp "b")
    --     let e' = evalTI testState (tiExpr ctx e)
    --     getType <$> e' `shouldBe` Right tBool

    context "Given a let expression" $ do
      it "returns the correct type" $ do
        let ctx = M.empty
        let leaf = ConstAnn sp "leaf" []
        let e1 = ConstAnn sp "node" [leaf, LitAnn sp (LitNum 2), leaf]
        let e2 = VarAnn sp "x" 
        let e = LetAnn sp "x" e1 e2
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s . getType <$> e' `shouldBe` Right tTreeNum

    context "Given a tick expression" $ do
      it "returns the type of the innser expression" $ do
        let ctx = M.fromList [("inner", toScheme tBool)]
        let e = TickAnn sp Nothing (VarAnn sp "inner")
        let e' = evalTI testState (tiExpr ctx e)
        getType <$> e' `shouldBe` Right tBool
    context "Give a coin expression" $ do
      it "returns a bool type" $ do
        let ctx = M.empty 
        let e = CoinAnn sp (1%2)
        let e' = evalTI testState (tiExpr ctx e)
        getType <$> e' `shouldBe` Right tBool

        
  describe "tiPatternVar" $ do
    context "given an id" $ do
      it "should bind the id" $ do
        let ctx = M.empty 
        let v = Id sp "a"
        let t = evalTI testState (tiPatternVar ctx v)
        t `shouldSatisfy` either (const False) (\(ctx, t) -> M.member "a" ctx)


  describe "tiPattern" $ do
    context "given a tree pattern" $ do
      it "should bind tree components and return tree type" $ do
        let ctx = M.empty
        let p = PatTreeNode sp (Id sp "l") (Id sp "v") (Id sp "r")
        let (r, state) = runTI testState (tiPattern ctx p)
        let isCorrect (ctx, t) = fromMaybe False (do
                                     l <- ctx M.!? "l"
                                     v <- ctx M.!? "v"
                                     r <- ctx  M.!? "r"
                                     return $ (l == toScheme t) && (r == toScheme t))
        let s = subst state
        let t' = bimap (apply s) (apply s . getType) <$> r
        t' `shouldSatisfy` either (const False) isCorrect


  describe "tiMatchArm" $ do
    context "given a valid match arm" $ do
      it "returns its type" $ do
        let ctx = M.empty
        let p = PatTreeNode sp (Id sp "l") (Id sp "v") (Id sp "r")
        let e = VarAnn sp "l" 
        let arm = MatchArmAnn sp p e
        let (r, state) = runTI testState (tiMatchArm ctx arm)
        let s = subst state
        let isCorrect s (MatchArm pat e) = apply s (getType pat) == apply s (getType e)
        r `shouldSatisfy` either (const False) (isCorrect s)


  describe "tiConst" $ do
    context "given a valid tree const" $ do
      it "returns a tree type" $ do
        let tt = tTreeNum
        let ctx = M.fromList [("a", toScheme tNum), ("b", toScheme tNum), ("l", toScheme tt),  ("r", toScheme tt)]
        let n1 = ConstAnn sp "node" [VarAnn sp "l", VarAnn sp "b", ConstAnn sp "leaf" []]
        let e = ConstAnn sp "node" [n1, VarAnn sp "a", VarAnn sp "r"]
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s . getType <$> e' `shouldBe` Right tt

    context "given an invalid tree const " $ do
      it "throws TypeMistmatch" $ do
        let tt = TAp Tree [tNum]
        let ctx = M.fromList [("l", toScheme tt), ("v", toScheme tNum), ("r", toScheme tNum)]
        let e = ConstAnn sp "node" [VarAnn sp "l", VarAnn sp "v", VarAnn sp "r"]
        let t = evalTI testState (tiExpr ctx e)
        t `shouldBe` Left (TypeMismatch tt tNum)

    context "given a valid tuple expression" $ do
      it "returns a prod type" $ do
        let tt = TAp Prod [tNum, tTreeNum]
        let ctx = M.fromList [("x", toScheme tNum), ("y", toScheme tTreeNum)]
        let e = ConstAnn sp "(,)" [VarAnn sp "x", VarAnn sp "y"]
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s . getType <$> e' `shouldBe` Right tt

    context "given a bool and a leaf const" $ do
      it "produces the right type" $ do
        let ctx = M.empty
        let e = ConstAnn sp "(,)" [ConstAnn sp "true" [], ConstAnn sp "leaf" []]
        let (e', state) = runTI testState (tiExpr ctx e)
        let s = subst state 
        apply s .getType <$> e' `shouldSatisfy` either (const False) (\(TAp Prod [tx, ty]) -> tx == tBool && isTreeType ty)
  describe "tiFun" $ do
    context "given a monomorphic tree construction function" $ do
      it "determines the type" $ do
        let tFun = [tTreeNum, tTreeNum] `fn` tTreeNum
        let ctx = M.empty
        let args = ["a", "b"]
        let body = ConstAnn sp "node" [VarAnn sp "a", LitAnn sp (LitNum 2), VarAnn sp "b"]
        let f = FunDef pfann "f" args body
        let (t, state) = runTI testState (tiFun ctx f)
        let s = subst state 
        apply s . fst <$> t `shouldBe` Right tFun
