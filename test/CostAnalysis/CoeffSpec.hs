{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.CoeffSpec where

import Test.Hspec

import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff

spec :: Spec
spec = do
  describe "except" $ do
    it "removes factors for the given variables, keeping constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let should = idxToSet [mix|x1^1,2|]
      let is = except [mix|x1^1,x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` should
  describe "varsExcept" $ do
    it "removes factors for the given variables and the constant factor." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let should = idxToSet [mix|x1^1|]
      let is = varsExcept [mix|x1^1,x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` should
  describe "restrict" $ do
    it "restricts factors to given variables, keeping constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let should = idxToSet [mix|x2^1,x3^1,2|]
      let is = restrict [mix|x1^1,x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` should
  describe "varsRestrict" $ do
    it "restricts factors to given variables, removing constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let should = idxToSet [mix|x2^1,x3^1|]
      let is = varsRestrict [mix|x1^1,x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` should                      
  describe "onlyVars" $ do
    it "checks wether an index contains only the given variables and no constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let is = onlyVars [mix|x1^1,x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` False
    it "checks wether an index contains only the given variables and no constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let is = onlyVars [mix|x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` False                                                   
    it "checks wether an index contains only the given variables and no constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let is = onlyVars [mix|x2^1,x3^1|] [x2, x3]
      is `shouldBe` True                                                                       
  describe "onlyVarsOrConst" $ do
    it "checks wether an index contains only the given variables or constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let is = onlyVarsOrConst [mix|x1^1,x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` False
    it "checks wether an index contains only the given variables and no constant factors." $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let is = onlyVarsOrConst [mix|x2^1,x3^1,2|] [x2, x3]
      is `shouldBe` True                                                   
    it "checks wether an index contains only the given variables and no constant factors" $ do
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let is = onlyVarsOrConst [mix|x2^1,x3^1|] [x2, x3]
      is `shouldBe` True
  describe "substitute" $ do
    it "substitutes the variables in an index for the given variables." $ do
      let (x1, x2) = ("x1", "x2")
      let (y1, y2) = ("y1", "y2")
      substitute [x1, x2] [y1, y2] [mix|x1^1,x2^2,2|]  `shouldBe` [mix|y1^1,y2^2,2|]
      

    
                                  
                                   
                                   

                                  
                                   
