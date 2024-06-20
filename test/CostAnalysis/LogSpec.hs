{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.LogSpec(spec) where

import Test.Hspec

import CostAnalysis.Log
import Prelude hiding ((!!))
import CostAnalysis.Potential(Coeff(Unknown),
                              IndexedCoeffs(..),
                              Constraint (..),
                              (!),
                              (!!))
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace (trace)

coeff idx = (idx, Unknown 0 "Q" "log" idx) 

_aRange = [0,1]
_bRange = [0,2]
args = LogPotArgs _aRange _bRange _aRange _bRange (-1 : _bRange)

spec :: Spec
spec = do
  describe "rsrcAnn" $ do
    it "generates a zero length resource annotation" $ do
      let id = 0
      let len = 0
      rsrcAnn args id "Q" len `shouldBe` IndexedCoeffs len (M.fromList [coeff [0], coeff [2]])
    it "generates a resource annotation of length 2" $ do
      let id = 0
      let len = 2
      let coeffs = M.fromList [coeff [1], coeff [2],
                               coeff[0,0,0], coeff[0,0,2],
                               coeff[1,0,0], coeff[1,0,2],
                               coeff[0,1,0], coeff[0,1,2],
                               coeff[1,1,0], coeff[1,1,2]]
      rsrcAnn args id "Q" len `shouldBe` IndexedCoeffs len coeffs
  describe "enumAnn" $ do
    it "enumerates indicies for a length of 3" $ do
      let idxs = [[0,1,1,0], [1,0,1,0], [1,1,1,0],
                  [0,1,1,2], [1,0,1,2], [1,1,1,2]]
      S.fromList (enumAnn args 3 False) `shouldBe` S.fromList idxs
  describe "forAllIdx" $ do
    it "generates a annoation array from the given indicies" $ do
      let idxs = [[1,1,0], [1,1,2]]
      length (forAllIdx args idxs [0,1] 1 "Q") `shouldBe` length idxs
  describe "cPlusConst" $ do
    it "generates the correct constraints" $ do
      let len = 1
      let q = rsrcAnn args 0 "Q" len
      let p = rsrcAnn args 1 "P" len
      let c = 1
      let should = EqPlusConst (q![0,2]) (p![0,2]) c :
                   [Eq (q![1]) (p![1]),
                    Eq (q![0,0]) (p![0,0]),
                    Eq (q![1,0]) (p![1,0]),
                    Eq (q![1,2]) (p![1,2])]
      cPlusConst args q p c `shouldBe` should
  describe "cMinusConst" $ do
    it "generates the correct constraints" $ do
      let len = 1
      let q = rsrcAnn args 0 "Q" len
      let p = rsrcAnn args 1 "P" len
      let c = 1
      let should = EqMinusConst (q![0,2]) (p![0,2]) c :
                   [Eq (q![1]) (p![1]),
                    Eq (q![0,0]) (p![0,0]),
                    Eq (q![1,0]) (p![1,0]),
                    Eq (q![1,2]) (p![1,2])]
      cMinusConst args q p c `shouldBe` should                          
  describe "cMinusVar" $ do
    it "generates the correct constraints" $ do
      let len = 1
      let q = rsrcAnn args 0 "Q" len
      let p = rsrcAnn args 1 "P" len
      let c = 1
      let should = EqMinusVar (q![0,2]) (p![0,2]) :
                   [Eq (q![1]) (p![1]),
                    Eq (q![0,0]) (p![0,0]),
                    Eq (q![1,0]) (p![1,0]),
                    Eq (q![1,2]) (p![1,2])]
      cMinusVar args q p `shouldBe` should                          
  describe "cPlusMulti" $ do
    it "generates the correct constraints" $ do
      let len = 1
      let q = rsrcAnn args 0 "Q" len
      let p = rsrcAnn args 1 "P" len
      let r = rsrcAnn args 2 "R" len
      let c = 1
      let should = [EqPlusMulti (q![1]) (p![1]) (r![1]),
                    EqPlusMulti (q![0,0]) (p![0,0]) (r![0,0]),
                    EqPlusMulti (q![0,2]) (p![0,2]) (r![0,2]),
                    EqPlusMulti (q![1,0]) (p![1,0]) (r![1,0]),
                    EqPlusMulti (q![1,2]) (p![1,2]) (r![1,2])]
      cPlusMulti args q p r `shouldBe` should
  describe "cLeaf" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn args 0 "Q" 0
      let q' = rsrcAnn args 1 "Q'" 1
      cLeaf args q q' `shouldBe` [EqSum (q![2]) [q'![1], q'![0,2]]]
  describe "cNode" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn args 0 "Q" 2
      let q' = rsrcAnn args 1 "Q'" 1
      let should = [Eq (q![1]) (q'![1]),
                    Eq (q![2]) (q'![1]),
                    Eq (q![1,0,0]) (q'![1]),
                    Eq (q![0,1,0]) (q'![1]),
                    Eq (q![0,0,0]) (q'![0,0]),
                    Eq (q![0,0,2]) (q'![0,2]),
                    Eq (q![1,1,0]) (q'![1,0]),
                    Eq (q![1,1,2]) (q'![1,2])]
      cNode args q q' `shouldBe` should
  describe "cPair" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn args 0 "Q" 1
      let q' = rsrcAnn args 1 "Q'" 1
      let should = [Eq (q![1]) (q'![1]),
                    Eq (q![0,0]) (q'![0,0]),
                    Eq (q![0,2]) (q'![0,2]),
                    Eq (q![1,0]) (q'![1,0]),
                    Eq (q![1,2]) (q'![1,2])]
      cPair args q q' `shouldBe` should
  describe "cMatchLeaf" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn args 0 "Q" 2
      let p = rsrcAnn args 1 "P" 1
      let should = [Eq (q![1]) (p![1]),
                    EqSum (p![0,0]) [q![0,0,0]],
                    EqSum (p![0,2]) [q![0,0,2]],
                    EqSum (p![1,0]) [q![1,0,0]],
                    EqSum (p![1,2]) [q![1,0,2]]]
      cMatchLeaf args q p `shouldBe` should
  describe "cMatchNode" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn args 0 "Q" 1
      let r = rsrcAnn args 1 "R" 2
      let should = [Eq (r![1]) (q![1]),
                    Eq (r![2]) (q![1]),
                    Eq (r![1,0,0]) (q![1]),
                    Eq (r![0,1,0]) (q![1]),
                    Eq (r![0,0,0]) (q![0,0]),
                    Eq (r![0,0,2]) (q![0,2]),
                    Eq (r![1,1,0]) (q![1,0]),
                    Eq (r![1,1,2]) (q![1,2])]
      cMatchNode args q r `shouldBe` should
  describe "cLetBase" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn args 0 "Q" 2
      let r = rsrcAnn args 1 "R" 1
      let p = rsrcAnn args 2 "P" 1
      let p' = rsrcAnn args 3 "P'" 0
      let should = [Eq (r![0,0]) (p'![0]),
                    Eq (r![0,2]) (p'![2]),
                    Eq (r![1]) (q![2]),
                    Eq (p![1]) (q![1]),
                    Eq (p![0,0]) (q![0,0,0]),
                    Eq (p![0,2]) (q![0,0,2]),
                    Eq (p![1,0]) (q![1,0,0]),
                    Eq (p![1,2]) (q![1,0,2]),
                    Eq (q![0,1,0]) (r![1,0]),
                    Eq (q![0,1,2]) (r![1,2])]
      cLetBase args q p r p' `shouldBe` should
  describe "cLet" $ do
    it "generates the correct constraints" $ do
      let neg = False
      let q = rsrcAnn args 0 "Q" 2
      let p = rsrcAnn args 1 "P" 1
      let p' = rsrcAnn args 2 "P'" 1
      let r = rsrcAnn args 3 "R" 2
      let ps = forAllIdx args (enumAnn args 2 neg) [4,5] 1 "P"
      let ps' = forAllIdx args (enumAnn args 2 neg) [6,7] 1 "P'"

      let cs = [Eq (p![1]) (q![1]),
                    Eq (p![0,0]) (q![0,0,0]),
                    Eq (p![0,2]) (q![0,0,2]),
                    Eq (p![1,0]) (q![1,0,0]),
                    Eq (p![1,2]) (q![1,0,2]),
                    Eq (r![1]) (q![2]),
                    Eq (r![2]) (p'![1]),
                    Eq (r![0,0,0]) (p'![0,0]),
                    Eq (r![0,0,2]) (p'![0,2]),
                    Eq (r![0,1,0]) (p'![1,0]),
                    Eq (r![0,1,2]) (p'![1,2]),
                    Eq (r![1,0,0]) (q![0,1,0]),
                    Eq (r![1,0,2]) (q![0,1,2]),
                    EqSum (q![1,1,0]) [ps!![1,1,0]![1,0],
                                       ps!![1,1,2]![1,0]],
                    EqSum (q![1,1,2]) [ps!![1,1,0]![1,2],
                                       ps!![1,1,2]![1,2]],
                    Eq (r![1,1,0]) (ps'!![1,1,0]![1,0]),
                    Zero (ps'!![1,1,0]![0,0]),
                    Zero (ps'!![1,1,0]![0,2]),
                    Zero (ps'!![1,1,0]![1,2]),
                    GeSum [ps!![1,1,0]![0,0],
                           ps!![1,1,0]![0,2],
                           ps!![1,1,0]![1,0],
                           ps!![1,1,0]![1,2]] (ps'!![1,1,0]![1,0]),
                    Impl (NotZero (ps!![1,1,0]![1,0])) (Le (ps'!![1,1,0]![1,0]) (ps!![1,1,0]![1,0])),
                    Impl (NotZero (ps!![1,1,0]![1,2])) (Le (ps'!![1,1,0]![1,0]) (ps!![1,1,0]![1,2])),
                    Eq (r![1,1,2]) (ps'!![1,1,2]![1,2]),
                    Zero (ps'!![1,1,2]![0,0]),
                    Zero (ps'!![1,1,2]![0,2]),
                    Zero (ps'!![1,1,2]![1,0]),
                    GeSum [ps!![1,1,2]![0,0],
                           ps!![1,1,2]![0,2],
                           ps!![1,1,2]![1,0],
                           ps!![1,1,2]![1,2]] (ps'!![1,1,2]![1,2]),
                    Impl (NotZero (ps!![1,1,2]![1,0])) (Le (ps'!![1,1,2]![1,2]) (ps!![1,1,2]![1,0])),
                    Impl (NotZero (ps!![1,1,2]![1,2])) (Le (ps'!![1,1,2]![1,2]) (ps!![1,1,2]![1,2]))]
      let is = S.fromList (cLet args neg q p p' ps ps' r)
      let should = S.fromList cs
      is `shouldBe` should
  -- describe "cWeakenVar" $ do
  --   it "generates the correct constraints" $ do
  --     let q = rsrcAnn args 0 "Q" 2
  --     let r = rsrcAnn args 1 "R" 1
  --     let should = [Eq (r![1]) (q![1]),
  --                   Eq (r![0,0]) (q![0,0,0]),
  --                   Eq (r![0,2]) (q![0,0,2]),
  --                   Eq (r![1,0]) (q![1,0,0])
  --                  ]
  --     cWeakenVar args q r `shouldBe` should
                   
      
      


