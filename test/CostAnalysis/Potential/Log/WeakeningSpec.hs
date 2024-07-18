{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.WeakeningSpec where

import Test.Hspec

import qualified Data.Set as S
import qualified Data.Vector as V
import Data.List(replicate)

import CostAnalysis.Potential.Log.Weakening
import Constants (treeT)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.Potential.Log.Helper

import Debug.Trace (trace)

traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x

spec :: Spec
spec = do
  describe "monoLe" $ do
    let (x, y) = ("x" , "y")
    context "(0,0,0) (1,0,0)" $ do
      it "is less then equal" $ do
        monoLe [mix||] [mix|x^1|] `shouldBe` True
    context "(0,0,0) (0,1,0)" $ do
      it "is less then equal" $ do
        monoLe [mix||] [mix|y^1|] `shouldBe` True
    context "(0,0,0) (0,0,2)" $ do
      it "is less then equal" $ do
        monoLe [mix||] [mix|2|] `shouldBe` True
    context "(0,0,2) (1,0,2)" $ do
      it "is less then equal" $ do                       
        monoLe [mix|2|] [mix|x^1,2|] `shouldBe` True
    context "(0,0,2) (0,0,0)" $ do
      it "is not less then equal" $ do                       
        monoLe [mix|2|] [mix||] `shouldBe` False
    context "(0,0,2) (0,1,2)" $ do
      it "is less then equal" $ do
        monoLe [mix|2|] [mix|y^1,2|] `shouldBe` True
    context "(0,1,0) (0,1,2)" $ do
      it "is less then equal" $ do                                      
        monoLe [mix|y^1|] [mix|y^1,2|] `shouldBe` True
    context "(0,1,0) (1,1,0)" $ do
      it "is less then equal" $ do
        monoLe [mix|y^1|] [mix|x^1,y^1|] `shouldBe` True
    context "(1,0,0) (1,0,2)" $ do
      it "is less then equal" $ do
        monoLe [mix|x^1|] [mix|x^1,2|] `shouldBe` True
    context "(1,0,0) (1,1,2)" $ do
      it "is less then equal" $ do
        monoLe [mix|x^1|] [mix|x^1,y^1,2|] `shouldBe` True
    context "(1,0,2) (1,1,2)" $ do
      it "is less then equal" $ do                              
        monoLe [mix|x^1,2|] [mix|x^1,y^1,2|] `shouldBe` True
    context "(1,0,2) (0,1,2)" $ do
      it "is not less then equal" $ do                              
        monoLe [mix|x^1,2|] [mix|y^1,2|] `shouldBe` False
    context "(0,1,2) (1,1,2)" $ do
      it "is less then equal" $ do                              
        monoLe [mix|y^1,2|] [mix|x^1,y^1,2|] `shouldBe` True
  describe "monotLattice" $ do
    it "generates the whole lattice as expert knowledge" $ do
      let args = [("x", treeT), ("y", treeT)]
      let p = rsrcAnn potArgs 0 "P" args
      let q = rsrcAnn potArgs 1 "Q" args
      let rows = map V.fromList 
                 [[0, 0, 1, 0,-1, 0, 0, 0, 0, 0],
                  [0, 0, 1, 0, 0,-1, 0, 0, 0, 0],
                  [0, 0, 1, 0, 0, 0,-1, 0, 0, 0],
                  [0, 0, 1, 0, 0, 0, 0,-1, 0, 0],
                  [0, 0, 1, 0, 0, 0, 0, 0,-1, 0],
                  [0, 0, 1, 0, 0, 0, 0, 0, 0,-1],
                  [0, 0, 0, 0, 1,-1, 0, 0, 0, 0],
                  [0, 0, 0, 0, 0,-1, 1, 0, 0, 0],
                  [0, 0, 0, 0,-1, 0, 0, 1, 0, 0],
                  [0, 0, 0, 0, 0,-1, 0, 1, 0, 0],
                  [0, 0, 0, 0, 0, 0, 0, 1,-1, 0],
                  [0, 0, 0, 0, 0,-1, 0, 0, 1, 0],
                  [0, 0, 0, 0, 0, 0,-1, 0, 0, 1],
                  [0, 0, 0, 0, 0,-1, 0, 0, 0, 1],
                  [0, 0, 0, 0, 0, 0, 0, 0,-1, 1],
                  [0, 0, 0, 1,-1, 0, 0, 0, 0, 0],
                  [0, 0, 0, 1, 0,-1, 0, 0, 0, 0],
                  [0, 0, 0, 1, 0, 0,-1, 0, 0, 0],
                  [0, 0, 1,-1, 0, 0, 0, 0, 0, 0]]
      let (asIs, bsIs) = monoLattice potArgs p q 
      S.fromList (V.toList asIs ) `shouldBe` S.fromList rows
      bsIs `shouldBe` replicate 19 0
  describe "logLemma" $ do
    it "generates expoert knowledge for all variable combinations according to the lemma" $ do
      let args = [("x", treeT), ("y", treeT), ("z", treeT)]
      let p = rsrcAnn potArgs 0 "P" args
      let q = rsrcAnn potArgs 1 "Q" args
      let rows = map V.fromList [[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1,-2, 0, 0, 1, 0, 0],
                  [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,-2, 0, 0, 1],
                  [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1]]
      let (asIs, bsIs) = logLemma potArgs p q 
      S.fromList (V.toList asIs ) `shouldBe` S.fromList rows
      bsIs `shouldBe` replicate 3 0
      
                                                
