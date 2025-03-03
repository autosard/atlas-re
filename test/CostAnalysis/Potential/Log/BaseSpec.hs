{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.BaseSpec(spec) where

import Test.Hspec
import CostAnalysis.Potential.Log.Helper 

import Prelude hiding ((!), (!!), (^))
import qualified Data.Map as M
import qualified Data.Set as S

import CostAnalysis.Potential.Log.Base 
import CostAnalysis.Potential.Log
import CostAnalysis.Coeff(Coeff(..), Factor(..), CoeffIdx(..), (^), idxToSet)
import CostAnalysis.RsrcAnn((!),(!!),RsrcAnn(..))
import Constants (treeT, boolT)
import CostAnalysis.Constraint ( zero )
import CostAnalysis.AnnIdxQuoter(mix)

spec :: Spec
spec = do
  describe "rsrcAnn" $ do
    it "generates a zero length resource annotation" $ do
      let id = 0
      let vars = []
      let should = RsrcAnn id vars "Q" "empty" (S.fromList [[mix|2|]])

      rsrcAnn id "Q" "empty" vars defaultRanges `shouldBe` should
    it "generates a resource annotation of length 2" $ do
      let id = 0
      let (x1, x2, x3) = ("x1", "x2", "x3")
      let vars = [x1, x2]
      let coeffs = S.fromList [Pure x1, Pure x2,
                               [mix|x1^1|], [mix|x1^1,1|],
                               [mix|x2^1|], [mix|x2^1,1|],
                               [mix|x1^1,x2^1|], [mix|x1^1,x2^1,1|],
                               [mix|2|],
                               [mix|x1^1|], [mix|x1^1, 2|],
                               [mix|x2^1|], [mix|x2^1,2|],
                               [mix|x1^1,x2^1|], [mix|x1^1,x2^1,2|]]
      let should = RsrcAnn id vars "Q" "2" coeffs
      rsrcAnn id "Q" "2" vars defaultRanges `shouldBe` should
