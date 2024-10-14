{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.NLog.WeakeningSpec where

import Test.Hspec

import qualified Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Vector as V
import Data.List(replicate)

import CostAnalysis.Potential.NLog.Weakening
import Constants (treeT)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.RsrcAnn
import CostAnalysis.Coeff
import CostAnalysis.Potential
import CostAnalysis.Potential.Log.Base hiding (rsrcAnn)
import CostAnalysis.Potential.Log.Helper
import Data.Set (Set)

x = "x"

table = [
         ([mix|x^(0,0,0)|], [mix|x^(0,0,1)|], False),
         ([mix|x^(0,0,0)|], [mix|x^(0,1,0)|], False),
         ([mix|x^(0,0,0)|], [mix|x^(1,0,0)|], False),
         ([mix|x^(0,0,0)|], [mix|x^(1,0,1)|], False),
         ([mix|x^(0,0,0)|], [mix|x^(1,1,0)|], False),
         
         ([mix|x^(0,0,1)|], [mix|x^(0,0,0)|], False),
         ([mix|x^(0,0,1)|], [mix|x^(0,1,0)|], False),
         ([mix|x^(0,0,1)|], [mix|x^(1,0,0)|], True), -- log <= n
         ([mix|x^(0,0,1)|], [mix|x^(1,0,1)|], True), 
         ([mix|x^(0,0,1)|], [mix|x^(1,1,0)|], False),

         ([mix|x^(0,1,0)|], [mix|x^(0,0,0)|], False),
         ([mix|x^(0,1,0)|], [mix|x^(0,0,1)|], True), -- log(n) <= log(n+1)
         ([mix|x^(0,1,0)|], [mix|x^(1,0,0)|], True), -- log <= n
         ([mix|x^(0,1,0)|], [mix|x^(1,0,1)|], False), -- 
         ([mix|x^(0,1,0)|], [mix|x^(1,1,0)|], True), -- n times
         
         ([mix|x^(1,0,0)|], [mix|x^(0,0,0)|], False), 
         ([mix|x^(1,0,0)|], [mix|x^(0,0,1)|], False),
         ([mix|x^(1,0,0)|], [mix|x^(0,1,0)|], False), 
         ([mix|x^(1,0,0)|], [mix|x^(1,0,1)|], False), 
         ([mix|x^(1,0,0)|], [mix|x^(1,1,0)|], False),

         ([mix|x^(1,0,1)|], [mix|x^(0,0,0)|], False),
         ([mix|x^(1,0,1)|], [mix|x^(0,0,1)|], False),
         ([mix|x^(1,0,1)|], [mix|x^(0,1,0)|], False),
         ([mix|x^(1,0,1)|], [mix|x^(1,0,0)|], False),
         ([mix|x^(1,0,1)|], [mix|x^(1,1,0)|], False),

         ([mix|x^(1,1,0)|], [mix|x^(0,0,0)|], False),
         ([mix|x^(1,1,0)|], [mix|x^(0,0,1)|], False),
         ([mix|x^(1,1,0)|], [mix|x^(0,1,0)|], False),
         ([mix|x^(1,1,0)|], [mix|x^(1,0,0)|], False),
         ([mix|x^(1,1,0)|], [mix|x^(1,0,1)|], True)
        ]

testRow :: (CoeffIdx, CoeffIdx, Bool) -> Expectation
testRow (i, j, should) = monoLe [x] i j `shouldBe` should

spec :: Spec
spec = do
  describe "monoLe" $ do
    it "covers all cases" $ do
      mapM_ testRow table
