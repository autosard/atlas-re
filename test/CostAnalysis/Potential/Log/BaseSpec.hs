{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.Log.BaseSpec(spec) where

import Test.Hspec
import CostAnalysis.Potential.Log.Helper

import Prelude hiding ((!), (!!), (^))
import qualified Data.Map as M

import CostAnalysis.Potential.Log.Base
import CostAnalysis.Potential.Log
import CostAnalysis.Coeff(Coeff(..), Factor(..), CoeffIdx(..), (^))
import CostAnalysis.RsrcAnn((!),(!!),RsrcAnn(..))
import Constants (treeT)

spec :: Spec
spec = do
  describe "rsrcAnn" $ do
    it "generates a zero length resource annotation" $ do
      let id = 0
      let vars = []
      let should = RsrcAnn vars (M.fromList [coeff [], coeff [Const 2]])
      rsrcAnn potArgs id "Q" vars `shouldBe` should
    it "generates a resource annotation of length 2" $ do
      let id = 0
      let vars = [("x1", treeT), ("x2", treeT)]
      let coeffs = M.fromList [coeff' "x1", coeff' "x2",
                               coeff [], coeff [Const 2],
                               coeff["x1"^1], coeff["x1"^1,Const 2],
                               coeff["x2"^1], coeff["x2"^1, Const 2],
                               coeff["x1"^1, "x2"^1], coeff["x1"^1, "x2"^1, Const 2]]
      rsrcAnn potArgs id "Q" vars `shouldBe` RsrcAnn vars coeffs
  describe "forAllCombinations" $ do
    it "generates a annoation array from the given variables and updates the id gen correctly" $ do
      let neg = False
      let combLeft = [("x1", treeT), ("x2", treeT)]
      let combRight = "x3"
      let annArgs = [("y1", treeT)]
      let idGen = 0
      let array = M.fromList [
            (arrIdx ["x1"^1, "x3"^1], rsrcAnn potArgs 2 "Q_(x1^1,x3^1)" annArgs),
            (arrIdx ["x1"^1, "x3"^1, Const 2], rsrcAnn potArgs 3 "Q_(2,x1^1,x3^1)" annArgs),
            (arrIdx ["x2"^1, "x3"^1], rsrcAnn potArgs 0 "Q_(x2^1,x3^1)" annArgs),
            (arrIdx ["x2"^1, "x3"^1, Const 2], rsrcAnn potArgs 1 "Q_(2,x2^1,x3^1)" annArgs),
            (arrIdx ["x1"^1, "x2"^1, "x3"^1], rsrcAnn potArgs 4 "Q_(x1^1,x2^1,x3^1)" annArgs),
            (arrIdx ["x1"^1, "x2"^1, "x3"^1, Const 2], rsrcAnn potArgs 5 "Q_(2,x1^1,x2^1,x3^1)" annArgs)]
      let finalId = 6
      forAllCombinations potArgs neg combLeft combRight idGen "Q" annArgs `shouldBe` (array, finalId)

