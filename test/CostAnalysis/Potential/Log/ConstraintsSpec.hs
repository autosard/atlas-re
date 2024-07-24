{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.ConstraintsSpec where

import Test.Hspec
import CostAnalysis.Potential.Log.Helper

import Prelude hiding ((!), (!!), (^))
import Data.Text(Text)
import qualified Data.Map as M
import qualified Data.Set as S

import CostAnalysis.Potential.Log.Constraints
import CostAnalysis.Potential.Log.Base hiding (rsrcAnn)
import CostAnalysis.Coeff(Coeff(..), Factor(..), CoeffIdx(..), (^))
import CostAnalysis.AnnIdxQuoter(mix)
import Constants (treeT)
import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn((!),(!!),RsrcAnn(..))

import Primitive(Id)

spec :: Spec
spec = do
  describe "cPlusConst" $ do
    it "generates the correct constraints" $ do
      let args = [("x", treeT)]
      let q = rsrcAnn 0 "Q" args
      let p = rsrcAnn 1 "P" args
      let c = 1
      let x = ("x" :: Text)
      let should = eqPlusConst (q![Const 2]) (p![Const 2]) c :
                   [eq (q!x) (p!x),
                    eq (q!empty) (p!empty),
                    eq (q!["x"^1]) (p!["x"^1]),
                    eq (q!["x"^1, Const 2]) (p!["x"^1, Const 2])]
      cPlusConst potArgs q p c `shouldBe` should
  describe "cMinusVar" $ do
    it "generates the correct constraints" $ do
      let args = [("x", treeT)]
      let q = rsrcAnn 0 "Q" args
      let p = rsrcAnn 1 "P" args
      let k = 0
      let c = 1
      let x = ("x" :: Text)
      let should = eqMinusVar (q![Const 2]) (p![Const 2]) k:
                   [eq (q!x) (p!x),
                    eq (q!empty) (p!empty),
                    eq (q!["x"^1]) (p!["x"^1]),
                    eq (q!["x"^1, Const 2]) (p!["x"^1, Const 2])]
      cMinusVar potArgs q p k `shouldBe` should
  describe "cPlusMulti" $ do
    it "generates the correct constraints" $ do
      let args = [("x", treeT)]
      let q = rsrcAnn 0 "Q" args
      let p = rsrcAnn 1 "P" args
      let r = rsrcAnn 2 "R" args
      let k = 0
      let c = 1
      let x = ("x" :: Text)
      
      let should = [eqPlusMulti (q!x) (p!x) (r!x) k,
                    eqPlusMulti (q!empty) (p!empty) (r!empty) k,
                    eqPlusMulti (q![Const 2]) (p![Const 2]) (r![Const 2]) k,
                    eqPlusMulti (q!["x"^1]) (p!["x"^1]) (r!["x"^1]) k,
                    eqPlusMulti (q!["x"^1, Const 2]) (p!["x"^1, Const 2]) (r!["x"^1, Const 2]) k]
      let is = cPlusMulti potArgs q p r k
      is `shouldBe` should
  describe "cEq" $ do
    it "generates the correct constraints for the leaf case" $ do
      let q = rsrcAnn 0 "Q" []
      let q' = rsrcAnn 1 "Q'" [("e", treeT)]
      let e = ("e" :: Id)
      let should = [eqSum (q![Const 2]) [q'!e, q'![Const 2]]]
      cEq potArgs q q' `shouldBe` should
    it "generates the correct constraints for the node case" $ do
      let [x1, x2] = ["x1", "x2"]
      let e = "e"
      let q = rsrcAnn 0 "Q" [(x1, treeT), (x2, treeT)]
      let q' = rsrcAnn 1 "Q'" [(e, treeT)]
      let should = [eq (q!x1) (q'!e),
                    eq (q!x2) (q'!e),
                    eq (q!["x1"^1]) (q'!e),
                    eq (q!["x2"^1]) (q'!e),
                    eq (q!empty) (q'!empty),
                    eq (q![Const 2]) (q'![Const 2]),
                    eq (q!["x1"^1, "x2"^1]) (q'!["e"^1]),
                    eq (q!["x1"^1, "x2"^1, Const 2]) (q'!["e"^1, Const 2]),
                    zero (q![mix|x2^1,2|]),
                    zero (q![mix|x1^1,2|])]
      cEq potArgs q q' `shouldBe` should
  describe "cEq" $ do
    it "generates the correct constraints for the pair case" $ do
      let (x, e) = ("x", "e")
      let q = rsrcAnn 0 "Q" [(x, treeT)]
      let q' = rsrcAnn 1 "Q'" [(e, treeT)]
      let should = [eq (q!x) (q'!e),
                    eq (q!empty) (q'!empty),
                    eq (q![Const 2]) (q'![Const 2]),
                    eq (q!["x"^1]) (q'!["e"^1]),
                    eq (q!["x"^1, Const 2]) (q'!["e"^1, Const 2])]
      cEq potArgs q q' `shouldBe` should
  describe "cMatch" $ do
    it "generates the correct constraints or the leaf case" $ do
      let (x1, x2) = ("x1" :: Text, "x2" :: Text) 
      let q = rsrcAnn 0 "Q" [(x1, treeT), (x2, treeT)]
      let p = rsrcAnn 1 "P" [(x1, treeT)]
      let should = [eq (q!x1) (p!x1),
                    eqSum (p![Const 2]) [q![Const 2], q!x2],
                    eqSum (p!empty) [q!empty],
                    eqSum (p!["x1"^1]) [q!["x1"^1]],
                    eqSum (p!["x1"^1,Const 2]) [q!["x1"^1, Const 2]]]
      cMatch potArgs q p x2 [] `shouldBe` should
    it "generates the correct constraints for the node case" $ do
      let (t, u, v) = ("t", "u", "v") 
      let q = rsrcAnn 0 "Q" [(t, treeT)]
      let r = rsrcAnn 1 "R" [(u, treeT), (v, treeT)]
      let should = [eq (r!u) (q!t),
                    eq (r!v) (q!t),
                    eq (r![mix|u^1|]) (q!t),
                    eq (r![mix|v^1|]) (q!t),
                    eq (r![mix||]) (q![mix||]),
                    eq (r![mix|2|]) (q![mix|2|]),
                    eq (r![mix|u^1,v^1|]) (q![mix|t^1|]),
                    eq (r![mix|u^1,v^1,2|]) (q![mix|t^1,2|]),
                    zero (r![mix|v^1,2|]),
                    zero (r![mix|u^1,2|])]
      cMatch potArgs q r t [(u, treeT), (v, treeT)] `shouldBe` should
  describe "cLetBase" $ do
    it "generates the correct constraints" $ do
      let (t1, t2) = ("t1", "t2")
      let q = rsrcAnn 0 "Q" [(t1, treeT), (t2, treeT)]
      let r = rsrcAnn 1 "R" [(t2, treeT)]
      let p = rsrcAnn 2 "P" [(t1, treeT)]
      let p' = rsrcAnn 3 "P'" []
      let should = [eq (r![mix||]) (p'![mix||]),
                    eq (r![mix|2|]) (p'![mix|2|]),
                    eq (r!t2) (q!t2),
                    eq (p!t1) (q!t1),
                    eq (p![mix||]) (q![mix||]),
                    eq (p![mix|2|]) (q![mix|2|]),
                    eq (p![mix|t1^1|]) (q![mix|t1^1|]),
                    eq (p![mix|t1^1,2|]) (q![mix|t1^1,2|]),
                    eq (q![mix|t2^1|]) (r![mix|t2^1|]),
                    eq (q![mix|t2^1,2|]) (r![mix|t2^1,2|])]
      cLetBase potArgs q p r p' `shouldBe` should
  describe "cLet" $ do
    it "generates the correct constraints" $ do
      let neg = False
      let (t1, t2, e) = ("t1", "t2", "e")
      let x = "x"
      let q = rsrcAnn 0 "Q" [(t1, treeT), (t2, treeT)]
      let p = rsrcAnn 1 "P" [(t1, treeT)]
      let p' = rsrcAnn 2 "P'" [(e, treeT)]
      let r = rsrcAnn 3 "R" [(t2, treeT), (x, treeT)]
      let ((ps, _), _) = forAllCombinations potArgs neg [(t2, treeT)] x 4 "P" [(t1, treeT)]
      let ((ps', _), _) = forAllCombinations potArgs neg [(t2, treeT)] x 6 "P'" [(e, treeT)]

      let cs = [eq (p!t1) (q!t1),
                    eq (p![mix||]) (q![mix||]),
                    eq (p![mix|2|]) (q![mix|2|]),
                    eq (p![mix|t1^1|]) (q![mix|t1^1|]),
                    eq (p![mix|t1^1,2|]) (q![mix|t1^1,2|]),
                    eq (r!t2) (q!t2),
                    eq (r!x) (p'!e),
                    eq (r![mix||]) (p'![mix||]),
                    eq (r![mix|2|]) (p'![mix|2|]),
                    eq (r![mix|x^1|]) (p'![mix|e^1|]),
                    eq (r![mix|x^1,2|]) (p'![mix|e^1,2|]),
                    eq (r![mix|t2^1|]) (q![mix|t2^1|]),
                    eq (r![mix|t2^1,2|]) (q![mix|t2^1,2|]),
                    eqSum (q![mix|t1^1,t2^1|]) [ps!![mix|t2^1,x^1|]![mix|t1^1|],
                                                ps!![mix|t2^1,x^1,2|]![mix|t1^1|]],
                    eqSum (q![mix|t1^1,t2^1,2|]) [ps!![mix|t2^1,x^1|]![mix|t1^1,2|],
                                                ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]],
                    eq (r![mix|t2^1,x^1|]) (ps'!![mix|t2^1,x^1|]![mix|e^1|]),
                    zero (ps'!![mix|t2^1,x^1|]![mix||]),
                    zero (ps'!![mix|t2^1,x^1|]![mix|2|]),
                    zero (ps'!![mix|t2^1,x^1|]![mix|e^1,2|]),
                    geSum [ps!![mix|t2^1,x^1|]![mix||],
                           ps!![mix|t2^1,x^1|]![mix|2|],
                           ps!![mix|t2^1,x^1|]![mix|t1^1|],
                           ps!![mix|t2^1,x^1|]![mix|t1^1,2|]]
                                 (ps'!![mix|t2^1,x^1|]![mix|e^1|]),
                    Impl (notZero (ps!![mix|t2^1,x^1|]![mix|t1^1|]))
                                 (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1|])),
                    Impl (notZero (ps!![mix|t2^1,x^1|]![mix|t1^1,2|]))
                                 (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1,2|])),
                    eq (r![mix|t2^1,x^1,2|]) (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]),
                    zero (ps'!![mix|t2^1,x^1,2|]![mix||]),
                    zero (ps'!![mix|t2^1,x^1,2|]![mix|2|]),
                    zero (ps'!![mix|t2^1,x^1,2|]![mix|e^1|]),
                    geSum [ps!![mix|t2^1,x^1,2|]![mix||],
                           ps!![mix|t2^1,x^1,2|]![mix|2|],
                           ps!![mix|t2^1,x^1,2|]![mix|t1^1|],
                           ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]] (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]),
                    Impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1|]))
                                 (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1|])),
                    Impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]))
                                 (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]))]
      let is = S.fromList (cLet potArgs neg q p p' ps ps' r x)
      let should = S.fromList cs
      is `shouldBe` should
  describe "cWeakenVar" $ do
    it "generates the correct constraints" $ do
      let (x1, x2) = ("x1", "x2")
      let q = rsrcAnn 0 "Q" [(x1, treeT), (x2, treeT)]
      let r = rsrcAnn 1 "R" [(x2, treeT)]
      let should = [eq (r!x2) (q!x2),
                    eq (r![mix||]) (q![mix||]),
                    eq (r![mix|2|]) (q![mix|2|]),
                    eq (r![mix|x2^1|]) (q![mix|x2^1|]),
                    eq (r![mix|x2^1,2|]) (q![mix|x2^1,2|])]
      cWeakenVar potArgs q r `shouldBe` should

