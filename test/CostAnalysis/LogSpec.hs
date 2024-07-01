{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.LogSpec(spec) where

import Test.Hspec

import CostAnalysis.Log
import Prelude hiding ((!), (!!), (^))
import Primitive(Id)

import CostAnalysis.Coeff(Coeff(..), Factor(..), CoeffIdx(..), (^))
import CostAnalysis.Solving(Constraint(..))
import CostAnalysis.Potential((!), RsrcAnn(..), (!!))
import CostAnalysis.AnnIdxQuoter(mix)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Text(Text)
import Debug.Trace (trace)

arrIdx = S.fromList

coeff :: [Factor] -> (CoeffIdx, Coeff)
coeff idx = let idx' = Mixed . S.fromList $ idx in
  (idx', Unknown 0 "Q" "log" idx')

coeff' :: Id -> (CoeffIdx, Coeff)
coeff' id = let idx = Pure id in
  (idx, Unknown 0 "Q" "log" idx)

_aRange = [0,1]
_bRange = [0,2]

potArgs :: LogPotArgs
potArgs = LogPotArgs _aRange _bRange _aRange _bRange (-1 : _bRange)

empty :: [Factor]
empty = []

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
      let vars = ["x1", "x2"]
      let coeffs = M.fromList [coeff' "x1", coeff' "x2",
                               coeff [], coeff [Const 2],
                               coeff["x1"^1], coeff["x1"^1,Const 2],
                               coeff["x2"^1], coeff["x2"^1, Const 2],
                               coeff["x1"^1, "x2"^1], coeff["x1"^1, "x2"^1, Const 2]]
      rsrcAnn potArgs id "Q" vars `shouldBe` RsrcAnn vars coeffs
  describe "forAllCombinations" $ do
    it "generates a annoation array from the given variables and updates the id gen correctly" $ do
      let neg = False
      let combLeft = ["x1", "x2"]
      let combRight = "x3"
      let annArgs = ["y1"]
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
  describe "cPlusConst" $ do
    it "generates the correct constraints" $ do
      let args = ["x"]
      let q = rsrcAnn potArgs 0 "Q" args
      let p = rsrcAnn potArgs 1 "P" args
      let c = 1
      let x = ("x" :: Text)
      let should = EqPlusConst (q![Const 2]) (p![Const 2]) c :
                   [Eq (q!x) (p!x),
                    Eq (q!empty) (p!empty),
                    Eq (q!["x"^1]) (p!["x"^1]),
                    Eq (q!["x"^1, Const 2]) (p!["x"^1, Const 2])]
      cPlusConst potArgs q p c `shouldBe` should
  describe "cMinusConst" $ do
    it "generates the correct constraints" $ do
      let args = ["x"]
      let q = rsrcAnn potArgs 0 "Q" args
      let p = rsrcAnn potArgs 1 "P" args
      let c = 1
      let x = ("x" :: Text)
      let should = EqMinusConst (q![Const 2]) (p![Const 2]) c :
                   [Eq (q!x) (p!x),
                    Eq (q!empty) (p!empty),
                    Eq (q!["x"^1]) (p!["x"^1]),
                    Eq (q!["x"^1, Const 2]) (p!["x"^1, Const 2])]
      cMinusConst potArgs q p c `shouldBe` should
  describe "cMinusVar" $ do
    it "generates the correct constraints" $ do
      let args = ["x"]
      let q = rsrcAnn potArgs 0 "Q" args
      let p = rsrcAnn potArgs 1 "P" args
      let c = 1
      let x = ("x" :: Text)
      let should = EqMinusVar (q![Const 2]) (p![Const 2]):
                   [Eq (q!x) (p!x),
                    Eq (q!empty) (p!empty),
                    Eq (q!["x"^1]) (p!["x"^1]),
                    Eq (q!["x"^1, Const 2]) (p!["x"^1, Const 2])]
      cMinusVar potArgs q p `shouldBe` should
  describe "cPlusMulti" $ do
    it "generates the correct constraints" $ do
      let args = ["x"]
      let q = rsrcAnn potArgs 0 "Q" args
      let p = rsrcAnn potArgs 1 "P" args
      let r = rsrcAnn potArgs 2 "R" args
      let c = 1
      let x = ("x" :: Text)
      
      let should = [EqPlusMulti (q!x) (p!x) (r!x),
                    EqPlusMulti (q!empty) (p!empty) (r!empty),
                    EqPlusMulti (q![Const 2]) (p![Const 2]) (r![Const 2]),
                    EqPlusMulti (q!["x"^1]) (p!["x"^1]) (r!["x"^1]),
                    EqPlusMulti (q!["x"^1, Const 2]) (p!["x"^1, Const 2]) (r!["x"^1, Const 2])]
      let is = cPlusMulti potArgs q p r 
      is `shouldBe` should
  describe "cLeaf" $ do
    it "generates the correct constraints" $ do
      let q = rsrcAnn potArgs 0 "Q" []
      let q' = rsrcAnn potArgs 1 "Q'" ["e"]
      let e = ("e" :: Id)
      let should = [EqSum (q![Const 2]) [q'!e, q'![Const 2]]]
      cLeaf potArgs q q' `shouldBe` should
  describe "cNode" $ do
    it "generates the correct constraints" $ do
      let [x1, x2] = ["x1", "x2"]
      let e = "e"
      let q = rsrcAnn potArgs 0 "Q" [x1, x2]
      let q' = rsrcAnn potArgs 1 "Q'" [e]
      let should = [Eq (q!x1) (q'!e),
                    Eq (q!x2) (q'!e),
                    Eq (q!["x1"^1]) (q'!e),
                    Eq (q!["x2"^1]) (q'!e),
                    Eq (q!empty) (q'!empty),
                    Eq (q![Const 2]) (q'![Const 2]),
                    Eq (q!["x1"^1, "x2"^1]) (q'!["e"^1]),
                    Eq (q!["x1"^1, "x2"^1, Const 2]) (q'!["e"^1, Const 2])]
      cNode potArgs q q' `shouldBe` should
  describe "cPair" $ do
    it "generates the correct constraints" $ do
      let (x, e) = ("x", "e")
      let q = rsrcAnn potArgs 0 "Q" [x]
      let q' = rsrcAnn potArgs 1 "Q'" [e]
      let should = [Eq (q!x) (q'!e),
                    Eq (q!empty) (q'!empty),
                    Eq (q![Const 2]) (q'![Const 2]),
                    Eq (q!["x"^1]) (q'!["e"^1]),
                    Eq (q!["x"^1, Const 2]) (q'!["e"^1, Const 2])]
      cPair potArgs q q' `shouldBe` should
  describe "cMatchLeaf" $ do
    it "generates the correct constraints" $ do
      let (x1, x2) = ("x1", "x2") 
      let q = rsrcAnn potArgs 0 "Q" [x1, x2]
      let p = rsrcAnn potArgs 1 "P" [x1]
      let should = [Eq (q!x1) (p!x1),
                    EqSum (p![Const 2]) [q![Const 2], q!x2],
                    EqSum (p!empty) [q!empty],
                    EqSum (p!["x1"^1]) [q!["x1"^1]],
                    EqSum (p!["x1"^1,Const 2]) [q!["x1"^1, Const 2]]]
      cMatchLeaf potArgs q p x2 `shouldBe` should
  describe "cMatchNode" $ do
    it "generates the correct constraints" $ do
      let (t, u, v) = ("t", "u", "v") 
      let q = rsrcAnn potArgs 0 "Q" [t]
      let r = rsrcAnn potArgs 1 "R" [u, v]
      let should = [Eq (r!u) (q!t),
                    Eq (r!v) (q!t),
                    Eq (r![mix|u^1|]) (q!t),
                    Eq (r![mix|v^1|]) (q!t),
                    Eq (r![mix||]) (q![mix||]),
                    Eq (r![mix|2|]) (q![mix|2|]),
                    Eq (r![mix|u^1,v^1|]) (q![mix|t^1|]),
                    Eq (r![mix|u^1,v^1,2|]) (q![mix|t^1,2|])]
      cMatchNode potArgs q r t u v`shouldBe` should
  describe "cLetBase" $ do
    it "generates the correct constraints" $ do
      let (t1, t2) = ("t1", "t2")
      let q = rsrcAnn potArgs 0 "Q" [t1, t2]
      let r = rsrcAnn potArgs 1 "R" [t2]
      let p = rsrcAnn potArgs 2 "P" [t1]
      let p' = rsrcAnn potArgs 3 "P'" []
      let should = [Eq (r![mix||]) (p'![mix||]),
                    Eq (r![mix|2|]) (p'![mix|2|]),
                    Eq (r!t2) (q!t2),
                    Eq (p!t1) (q!t1),
                    Eq (p![mix||]) (q![mix||]),
                    Eq (p![mix|2|]) (q![mix|2|]),
                    Eq (p![mix|t1^1|]) (q![mix|t1^1|]),
                    Eq (p![mix|t1^1,2|]) (q![mix|t1^1,2|]),
                    Eq (q![mix|t2^1|]) (r![mix|t2^1|]),
                    Eq (q![mix|t2^1,2|]) (r![mix|t2^1,2|])]
      cLetBase potArgs q p r p' `shouldBe` should
  describe "cLet" $ do
    it "generates the correct constraints" $ do
      let neg = False
      let (t1, t2, e) = ("t1", "t2", "e")
      let x = "x"
      let q = rsrcAnn potArgs 0 "Q" [t1, t2]
      let p = rsrcAnn potArgs 1 "P" [t1]
      let p' = rsrcAnn potArgs 2 "P'" [e]
      let r = rsrcAnn potArgs 3 "R" [t2, x]
      let (ps, _) = forAllCombinations potArgs neg [t2] x 4 "P" [t1]
      let (ps', _) = forAllCombinations potArgs neg [t2] x 6 "P'" [e]

      let cs = [Eq (p!t1) (q!t1),
                    Eq (p![mix||]) (q![mix||]),
                    Eq (p![mix|2|]) (q![mix|2|]),
                    Eq (p![mix|t1^1|]) (q![mix|t1^1|]),
                    Eq (p![mix|t1^1,2|]) (q![mix|t1^1,2|]),
                    Eq (r!t2) (q!t2),
                    Eq (r!x) (p'!e),
                    Eq (r![mix||]) (p'![mix||]),
                    Eq (r![mix|2|]) (p'![mix|2|]),
                    Eq (r![mix|x^1|]) (p'![mix|e^1|]),
                    Eq (r![mix|x^1,2|]) (p'![mix|e^1,2|]),
                    Eq (r![mix|t2^1|]) (q![mix|t2^1|]),
                    Eq (r![mix|t2^1,2|]) (q![mix|t2^1,2|]),
                    EqSum (q![mix|t1^1,t2^1|]) [ps!![mix|t2^1,x^1|]![mix|t1^1|],
                                                ps!![mix|t2^1,x^1,2|]![mix|t1^1|]],
                    EqSum (q![mix|t1^1,t2^1,2|]) [ps!![mix|t2^1,x^1|]![mix|t1^1,2|],
                                                ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]],
                    Eq (r![mix|t2^1,x^1|]) (ps'!![mix|t2^1,x^1|]![mix|e^1|]),
                    Zero (ps'!![mix|t2^1,x^1|]![mix||]),
                    Zero (ps'!![mix|t2^1,x^1|]![mix|2|]),
                    Zero (ps'!![mix|t2^1,x^1|]![mix|e^1,2|]),
                    GeSum [ps!![mix|t2^1,x^1|]![mix||],
                           ps!![mix|t2^1,x^1|]![mix|2|],
                           ps!![mix|t2^1,x^1|]![mix|t1^1|],
                           ps!![mix|t2^1,x^1|]![mix|t1^1,2|]]
                                 (ps'!![mix|t2^1,x^1|]![mix|e^1|]),
                    Impl (NotZero (ps!![mix|t2^1,x^1|]![mix|t1^1|]))
                                 (Le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1|])),
                    Impl (NotZero (ps!![mix|t2^1,x^1|]![mix|t1^1,2|]))
                                 (Le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1,2|])),
                    Eq (r![mix|t2^1,x^1,2|]) (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]),
                    Zero (ps'!![mix|t2^1,x^1,2|]![mix||]),
                    Zero (ps'!![mix|t2^1,x^1,2|]![mix|2|]),
                    Zero (ps'!![mix|t2^1,x^1,2|]![mix|e^1|]),
                    GeSum [ps!![mix|t2^1,x^1,2|]![mix||],
                           ps!![mix|t2^1,x^1,2|]![mix|2|],
                           ps!![mix|t2^1,x^1,2|]![mix|t1^1|],
                           ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]] (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]),
                    Impl (NotZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1|]))
                                 (Le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1|])),
                    Impl (NotZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]))
                                 (Le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]))]
      let is = S.fromList (cLet potArgs neg q p p' ps ps' r x)
      let should = S.fromList cs
      is `shouldBe` should
  describe "cWeakenVar" $ do
    it "generates the correct constraints" $ do
      let (x1, x2) = ("x1", "x2")
      let q = rsrcAnn potArgs 0 "Q" [x1,x2]
      let r = rsrcAnn potArgs 1 "R" [x2]
      let should = [Eq (r!x2) (q!x2),
                    Eq (r![mix||]) (q![mix||]),
                    Eq (r![mix|2|]) (q![mix|2|]),
                    Eq (r![mix|x2^1|]) (q![mix|x2^1|]),
                    Eq (r![mix|x2^1,2|]) (q![mix|x2^1,2|])]
      cWeakenVar potArgs q r `shouldBe` should
                   
      
      


