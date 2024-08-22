{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.PotentialSpec(spec) where

import Test.Hspec
import CostAnalysis.Potential.Log.Helper

import qualified Data.Set as S

import CostAnalysis.Potential
import CostAnalysis.Potential.Log
import CostAnalysis.Coeff
import CostAnalysis.RsrcAnn
import Constants (treeT, boolT)
import CostAnalysis.Constraint 
import CostAnalysis.AnnIdxQuoter(mix)

spec :: Spec
spec = do
  describe "defaultNegAnn" $ do
    it "generates an annotation with coeffients in the default negative range." $ do
      let id = 0
      let x = "x"
      let y = "y"
      let vars = [(x, treeT)]
      let varsNonTree = (y, boolT):vars
      let coeffs = S.fromList [Pure x, [mix|x^1|], [mix|x^1,1|], [mix|x^1,2|], [mix|2|]]
      let should = RsrcAnn id vars "Q" "" coeffs
      defaultNegAnn pot id "Q" "" varsNonTree `shouldBe` should
  describe "emptyAnn" $ do
    it "generates an empty annotation with the correct arguments" $ do
      let id = 0
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let vars = [(x1, treeT), (x2, treeT)]
      let varsNonTree = (x3, boolT):vars
      let should = RsrcAnn id vars "Q" "" S.empty
      emptyAnn pot id "Q" "" varsNonTree `shouldBe` should
  describe "eqExceptConst" $ do
    it "generates the correct equality constraints" $ do
      let (x1, x2) = ("x1", "x2")
      let vars = [(x1, treeT), (x2, treeT)]
      let q_ = RsrcAnn 0 vars "Q" "" S.empty
      let p = RsrcAnn 1 vars "P" "" $ S.fromList [[mix|2|], [mix|x1^1|], [mix|x2^1|]]
      let (q, cs) = eqExceptConst pot q_ p
      let should = [Eq (q![mix|x1^1|]) (p![mix|x1^1|]),
                    Eq (q![mix|x2^1|]) (p![mix|x2^1|])]
      cs `shouldBe` should
  describe "eqPlus" $ do
    it "generates the correct constraints" $ do
      let (x1, x2) = ("x1", "x2")
      let vars = [(x1, treeT), (x2, treeT)]
      let q_ = RsrcAnn 0 vars "Q" "" S.empty
      let p = RsrcAnn 1 vars "P" "" $ S.fromList [[mix|2|], [mix|x1^1|], [mix|x2^1|]]
      let (q, cs) = eqPlus pot q_ p (ConstTerm 1)
      let should = [Eq (q![mix|2|]) (Sum [(p![mix|2|]), ConstTerm 1]),
                    Eq (q![mix|x1^1|]) (p![mix|x1^1|]),
                    Eq (q![mix|x2^1|]) (p![mix|x2^1|])]
      cs `shouldBe` should
  describe "eqMinus" $ do
    it "generates the correct constraints" $ do
      let (x1, x2) = ("x1", "x2")
      let vars = [(x1, treeT), (x2, treeT)]
      let k = VarTerm 0
      let q_ = RsrcAnn 0 vars "Q" "" S.empty
      let p = RsrcAnn 1 vars "P" "" $ S.fromList [[mix|2|], [mix|x1^1|], [mix|x2^1|]]
      let (q, cs) = eqMinus pot q_ p k                                                      
      let should = [Eq (q![mix|2|]) (Diff [(p![mix|2|]), k]),
                    Eq (q![mix|x1^1|]) (p![mix|x1^1|]),
                    Eq (q![mix|x2^1|]) (p![mix|x2^1|])]
      cs `shouldBe` should
  describe "forAllCombinations" $ do
    it "generates all requried combinations" $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let vars = [(x1, treeT), (x2, treeT)]
      let q = defaultAnn pot 0 "Q" "" vars
      let should = [[mix|x2^1,x3^1|], [mix|x2^1,x3^1,1|], [mix|x2^1,x3^1,2|], [mix|x2^1,x3^1|], [mix|x2^1,1|], [mix|x2^1,2|]]
      S.fromList (forAllCombinations q [x2] (_aRange, _bRange) x3) `shouldBe` S.fromList should
      
                             
                                 
                               
