{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.WeakeningSpec where

import Test.Hspec

import qualified Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Vector as V
import Data.List(replicate)

import CostAnalysis.Potential.Log.Weakening
import Constants (treeT)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.RsrcAnn
import CostAnalysis.Coeff
import CostAnalysis.Potential
import CostAnalysis.Potential.Log.Base hiding (rsrcAnn)
import CostAnalysis.Potential.Log.Helper
import Data.Set (Set)

spec :: Spec
spec = do
  describe "monoLe" $ do
    let (x, y) = ("x" , "y")
    context "(0,0,0) (1,0,0)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix||] [mix|x^1|] `shouldBe` True
    context "(0,0,0) (0,1,0)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix||] [mix|y^1|] `shouldBe` True
    context "(0,0,0) (0,0,2)" $ do
      it "is less then equal" $ do
        monoLe [x, y] [mix||] [mix|2|] `shouldBe` True
    context "(0,0,2) (1,0,2)" $ do
      it "is less then equal" $ do                       
        monoLe [x,y] [mix|2|] [mix|x^1,2|] `shouldBe` True
    context "(0,0,2) (0,0,0)" $ do
      it "is not less then equal" $ do                       
        monoLe [x,y] [mix|2|] [mix||] `shouldBe` False
    context "(0,0,2) (0,1,2)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix|2|] [mix|y^1,2|] `shouldBe` True
    context "(0,1,0) (0,1,2)" $ do
      it "is less then equal" $ do                                      
        monoLe [x,y] [mix|y^1|] [mix|y^1,2|] `shouldBe` True
    context "(0,1,0) (1,1,0)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix|y^1|] [mix|x^1,y^1|] `shouldBe` True
    context "(1,0,0) (1,0,2)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix|x^1|] [mix|x^1,2|] `shouldBe` True
    context "(1,0,0) (1,1,2)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix|x^1|] [mix|x^1,y^1,2|] `shouldBe` True
    context "(1,0,2) (1,1,2)" $ do
      it "is less then equal" $ do                              
        monoLe [x,y] [mix|x^1,2|] [mix|x^1,y^1,2|] `shouldBe` True
    context "(1,0,2) (0,1,2)" $ do
      it "is not less then equal" $ do                              
        monoLe [x,y] [mix|x^1,2|] [mix|y^1,2|] `shouldBe` False
    context "(0,1,2) (1,1,2)" $ do
      it "is less then equal" $ do                              
        monoLe [x,y] [mix|y^1,2|] [mix|x^1,y^1,2|] `shouldBe` True
    context "(0,1,0,0) (0,1,1,0)" $ do
      it "is less then equal" $ do
        monoLe [x,y] [mix|x^1|] [mix|x^1,y^1|] `shouldBe` True
  describe "monotLattice" $ do
    context "given length 0 annotations" $ do
      it "generates the whole lattice as expert knowledge" $ do
        let args = []
        let p = defaultAnn pot 0 "P" "" args
        let q = fromAnn 1 "Q" "" p
        let rows = []
        let (asIs, bsIs) = monoLattice args (definedIdxs p)
        S.fromList (V.toList asIs ) `shouldBe` S.fromList rows
        bsIs `shouldBe` []
    context "given length 1 annotations" $ do
      it "generates the whole lattice as expert knowledge" $ do
        let args = [("x", treeT)]
        let p = defaultAnn pot 0 "P" "" args
        let q = fromAnn 1 "Q" "" p
        let rows = map V.fromList [
              -- (x),(x^1,1),(2),(x^1,2),(x^1)
              [0,-1, 1, 0, 0],
              [0, 1, 0,-1, 0],
              [0, 0, 1,-1, 0],
              [0, 0, 0,-1, 1],
              [0,-1, 0, 0, 1]]
        let (asIs, bsIs) = monoLattice (map fst args) (definedIdxs p)
        S.fromList (V.toList asIs ) `shouldBe` S.fromList rows
        bsIs `shouldBe` replicate 5 0
    context "given length 2 annotations" $ do
      it "generates the whole lattice as expert knowledge" $ do
        let args = [("x", treeT), ("y", treeT)]
        let p = defaultAnn pot 0 "P" "" args
        let q = fromAnn 1 "Q" "" p
        let rows = map V.fromList
        -- (x),(y),(x^1,1),(y^1,x^1,1),(y^1,1),(2),(x^1,2),(y^1,x^1,2),(y^1,2),(x^1),(y^1,x^1),(y^1)]
                   [[0, 0, 1,-1, 0, 0, 0, 0, 0, 0, 0, 0],
                    [0, 0, 1, 0, 0, 0,-1, 0, 0, 0, 0, 0],
                    [0, 0, 1, 0, 0, 0, 0,-1, 0, 0, 0, 0],
                    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0,-1, 0],

                    [0, 0, 0, 1, 0, 0, 0,-1, 0, 0, 0, 0],


                    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0,-1, 0],
                    [0, 0, 0, 0, 1, 0, 0,-1, 0, 0, 0, 0],
                    [0, 0, 0, 0, 1, 0, 0, 0,-1, 0, 0, 0],
                    [0, 0, 0,-1, 1, 0, 0, 0, 0, 0, 0, 0],

                    [0, 0, 0, 0,-1, 1, 0, 0, 0, 0, 0, 0],
                    [0, 0, 0,-1, 0, 1, 0, 0, 0, 0, 0, 0],
                    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0,-1, 0],                    
                    [0, 0,-1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
                    [0, 0, 0, 0, 0, 1,-1, 0, 0, 0, 0, 0],
                    [0, 0, 0, 0, 0, 1, 0,-1, 0, 0, 0, 0],
                    [0, 0, 0, 0, 0, 1, 0, 0,-1, 0, 0, 0],
                    
                    [0, 0, 0, 0, 0, 0, 1,-1, 0, 0, 0, 0],
                    [0, 0, 0,-1, 0, 0, 1, 0, 0, 0, 0, 0],

                    [0, 0, 0,-1, 0, 0, 0, 0, 1, 0, 0, 0],
                    [0, 0, 0, 0, 0, 0, 0,-1, 1, 0, 0, 0],


                    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1,-1, 0],
                    [0, 0,-1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
                    [0, 0, 0,-1, 0, 0, 0, 0, 0, 1, 0, 0],
                    [0, 0, 0, 0, 0, 0,-1, 0, 0, 1, 0, 0],
                    [0, 0, 0, 0, 0, 0, 0,-1, 0, 1, 0, 0],

                    [0, 0, 0,-1, 0, 0, 0, 0, 0, 0, 1, 0],
                    [0, 0, 0, 0, 0, 0, 0,-1, 0, 0, 1, 0],

                    [0, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 1],
                    [0, 0, 0, 0,-1, 0, 0, 0, 0, 0, 0, 1],
                    [0, 0, 0, 0, 0, 0, 0,-1, 0, 0, 0, 1],
                    [0, 0, 0, 0, 0, 0, 0, 0,-1, 0, 0, 1],
                    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-1, 1]]
        let (asIs, bsIs) = monoLattice (map fst args) (definedIdxs p)
        S.fromList (V.toList asIs ) S.\\ S.fromList rows `shouldBe` S.empty
        S.fromList rows  S.\\ S.fromList (V.toList asIs ) `shouldBe` S.empty
        S.fromList (V.toList asIs ) `shouldBe` S.fromList rows
        bsIs `shouldBe` replicate 32 0
    -- context "given length 2 annotations" $ do
    --   it "contains some examples" $ do
    --     let args = [("cr", treeT), ("bl", treeT), ("br", treeT)]
    --     let p = defaultAnn pot 0 "P" "" args
    --     -- (bl),(br),(cr),(bl^1,1),(br^1,bl^1,1),(cr^1,br^1,bl^1,1),(cr^1,bl^1,1),(br^1,1),(cr^1,br^1,1),(cr^1,1),(2),(bl^1,2),(br^1,bl^1,2),(cr^1,br^1,bl^1,2),(cr^1,bl^1,2),(br^1,2),(cr^1,br^1,2),(cr^1,2),(bl^1),(br^1,bl^1),(cr^1,br^1,bl^1),(cr^1,bl^1),(br^1),(cr^1,br^1),(cr^1)
    --     let rows = map V.fromList [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0]]
    --     let (asIs, bsIs) = monoLattice (definedIdxs p)
    --     S.isSubsetOf (S.fromList rows) (S.fromList (V.toList asIs)) `shouldBe` True
    --     bsIs `shouldBe` replicate 100 0      
  describe "logLemma" $ do
    context "given length 0 annotations" $ do
      it "returns the empty expert knowledge matrix." $ do
        let args = []
        let p = defaultAnn pot 0 "P" "" args
        let q = fromAnn 1 "Q" "" p
        let (asIs, bsIs) = logLemma (map fst args) (definedIdxs p)
        V.toList asIs `shouldBe` []
        bsIs `shouldBe` []
    context "given length 1 annotations" $ do
      it "returns the empty expert knowledge matrix." $ do
        let args = [("x", treeT)]
        let p = defaultAnn pot 0 "P" "" args
        let q = fromAnn 1 "Q" "" p
        let (asIs, bsIs) = logLemma (map fst args) (definedIdxs p)
        V.toList asIs `shouldBe` []
        bsIs `shouldBe` []        
    context "given length 3 annotations" $ do
      it "generates expert knowledge for all variable combinations according to the lemma" $ do
        let args = [("x", treeT), ("y", treeT), ("z", treeT)]
        let p = defaultAnn pot 0 "P" "" args
        let q = fromAnn 1 "Q" "" p
        -- [(x),(y),(z),(x^1,1),(y^1,x^1,1),(z^1,y^1,x^1,1),(z^1,x^1,1),(y^1,1),(z^1,y^1,1),(z^1,1),(2),(x^1,2),(y^1,x^1,2),(z^1,y^1,x^1,2),(z^1,x^1,2),(y^1,2),(z^1,y^1,2),(z^1,2),(x^1),(y^1,x^1),(z^1,y^1,x^1),(z^1,x^1),(y^1),(z^1,y^1),(z^1)]
        -- let rows = map V.fromList [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1,-2, 0, 0, 1, 0, 0],
        --                            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,-2, 0, 0, 1],
        --                            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,-2, 1],
        --                            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0,-2, 0, 0, 1, 0],
        --                            [0, 0, 0, 0, 0, 0, 0, 1,-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
        --                            [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0,-2, 0, 0, 0, 0, 0, 0, 0, 0],
        --                            [0, 0, 0, 0, 0, 0, 0, 1,-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        --                            [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0,-2, 0, 0, 0, 0, 0, 0, 0, 0],
        --                            [0, 0, 0, 1,-2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        --                            [0, 0, 0, 1, 0,-2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        --                            [0, 0, 0, 1, 0, 0,-2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        --                            [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0,-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        --                            [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0,-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        --                            [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0,-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
        
        
        let (asIs, bsIs) = logLemma (map fst args) (definedIdxs p)
--        (S.fromList rows S.\\ S.fromList (V.toList asIs )) `shouldBe` S.empty
        mapM_ (\row -> let (x,y,ys) = l2xyRowToCoeffs (_coeffs p) row in addIdxs x y `shouldBe` ys) asIs
        --S.fromList (V.toList asIs ) `shouldBe` S.fromList rows
        bsIs `shouldBe` replicate 36 0

l2xyRowToCoeffs :: Set CoeffIdx -> V.Vector Int -> (CoeffIdx, CoeffIdx, CoeffIdx)
l2xyRowToCoeffs idxs row = (x, y, ys)
  where [x, y] = V.toList $ V.map (`S.elemAt` idxs) $ V.findIndices (==1) row
        [ys] = V.toList $ V.map (`S.elemAt` idxs) $ V.findIndices (== (-2)) row
