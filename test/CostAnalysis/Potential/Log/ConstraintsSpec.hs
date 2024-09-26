{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.ConstraintsSpec where

import Test.Hspec
import CostAnalysis.Potential.Log.Helper

import Prelude hiding ((!), (!!), (^), sum)
import Data.Text(Text)
import qualified Data.Map as M
import qualified Data.Set as S

import CostAnalysis.Potential.Log.Constraints
import CostAnalysis.Potential(defaultAnn, emptyAnn, forAllCombinations)
import CostAnalysis.Coeff(Coeff(..), Factor(..), CoeffIdx(..), (^))
import CostAnalysis.AnnIdxQuoter(mix)
import Constants (treeT)
import CostAnalysis.Constraint
import Ast (PositionedExprAnn(PositionedExprAnn), ExprSrc (Loc), Expr (ConstAnn, VarAnn), PositionedExpr)
import CostAnalysis.RsrcAnn((!),(!!),(!?),RsrcAnn(..))

import Primitive(Id)
import Parsing.Program (initialPos)

import Debug.Trace (trace)

import Typing.Type 
traceShow s x = Debug.Trace.trace (s ++ ": " ++ show x) x
tNum = TAp Num []
tTreeNum = TAp Tree [tNum]
sp = initialPos "test.ml"
posAnn = PositionedExprAnn (Loc sp) tTreeNum S.empty  

spec :: Spec
spec = do
  describe "cConst" $ do
    it "generates the correct constraints for the leaf case" $ do
      let q = defaultAnn pot 0 "Q" "" []
      let q' = defaultAnn pot 1 "Q'" "" [("e", treeT)]
      let expr = ConstAnn posAnn "leaf" [] :: PositionedExpr
      let e = ("e" :: Id)
      let should = concat [
            eqSum (q![mix|2|]) [q'![mix|2|], q'![mix|e^1,1|], q'!e],
            zero (q'![mix|e^1,2|])]
      case cConst expr q q' of
            Right cs -> (S.fromList cs) `shouldBe` S.fromList should
            Left err -> return ()
    it "generates the correct constraints for the node case" $ do
      let [x1, x2] = ["x1", "x2"]
      let e = "e"
      let expr = ConstAnn posAnn "node" [VarAnn posAnn x1, VarAnn posAnn "v", VarAnn posAnn x2] :: PositionedExpr
      let q = defaultAnn pot 0 "Q" "" [(x1, treeT), (x2, treeT)]
      let q' = defaultAnn pot 1 "Q'" "" [(e, treeT)]
      let should = concat [eq (q!x1) (q'!e),
                    eq (q!x2) (q'!e),
                    eq (q!["x1"^1]) (q'!e),
                    eq (q!["x2"^1]) (q'!e),
                    eq (q![Const 2]) (q'![Const 2]),
                    eq (q!["x1"^1, "x2"^1]) (q'!["e"^1]),
                    eq (q!["x1"^1, "x2"^1, Const 1]) (q'!["e"^1, Const 1]),
                    eq (q!["x1"^1, "x2"^1, Const 2]) (q'!["e"^1, Const 2]),
                    zero (q![mix|x2^1,1|]),
                    zero (q![mix|x2^1,2|]),
                    zero (q![mix|x1^1,1|]),
                    zero (q![mix|x1^1,2|])]
      case cConst expr q q' of
            Right cs -> (S.fromList cs) `shouldBe` S.fromList should
            Left err -> return ()
  describe "cMatch" $ do
    it "generates the correct constraints or the leaf case" $ do
      let (x1, x2) = ("x1", "x2") 
      let q = defaultAnn pot 0 "Q" "" [(x1, treeT), (x2, treeT)]
      let p = emptyAnn pot 1 "P" "" [(x1, treeT)]
      
      let (pDef, isCs) = cMatch q p x2 []
      let cs = concat [eq (pDef!x1) (q!x1) ,
                    eqSum (pDef![Const 2]) [q!x2,q![mix|x2^1,1|],q![mix|2|]],
                    eqSum (pDef![Const 3]) [q![mix|x2^1,2|]],
                    eqSum (pDef!["x1"^1]) [q!["x1"^1]],
                    eqSum (pDef![mix|x1^1,2|]) [q![mix|x1^1,x2^1,1|], q![mix|x1^1,2|]],
                    eqSum (pDef!["x1"^1,Const 1]) [q!["x1"^1, Const 1],q![mix|x1^1,x2^1|]],
                    eqSum (pDef!["x1"^1,Const 3]) [q![mix|x1^1,x2^1,2|]]]
                  
      let pShould = RsrcAnn 1 [(x1, treeT)] "P" "" $ S.fromList [
            Pure x1,
            [mix|2|],
            [mix|3|],
            [mix|x1^1|],
            [mix|x1^1,1|],
            [mix|x1^1,2|],
            [mix|x1^1,3|]]
      S.fromList isCs `shouldBe` S.fromList cs
      pDef `shouldBe` pShould
    it "generates the correct constraints for the node case" $ do
      let (t, u, v) = ("t", "u", "v") 
      let q = defaultAnn pot 0 "Q" "" [(t, treeT)]
      let r_ = emptyAnn pot 1 "R" "" [(u, treeT), (v, treeT)]
      let (r, isCs) = cMatch q r_ t [u, v]
      let cs = concat [eq (r!u) (q!t),
                    eq (r!v) (q!t),
                    eq (r![mix|u^1|]) (q!t),
                    eq (r![mix|v^1|]) (q!t),
                    eq (r![mix|2|]) (q![mix|2|]),
                    eq (r![mix|u^1,v^1|]) (q![mix|t^1|]),
                    eq (r![mix|u^1,v^1,1|]) (q![mix|t^1,1|]),
                    eq (r![mix|u^1,v^1,2|]) (q![mix|t^1,2|])]
      S.fromList isCs `shouldBe` S.fromList cs         
  describe "cLetBindingBase" $ do
    it "generates the correct constraints" $ do
      let (t1, t2) = ("t1", "t2")
      let q = defaultAnn pot 0 "Q" "" [(t1, treeT), (t2, treeT)]
      let p_ = emptyAnn pot 1 "P" "" [(t1, treeT)]
      let (p, isCs) = cLetBindingBase q p_ 
      let cs = concat [
            eq (p!t1) (q!t1),
            eq (p![mix|2|]) (q![mix|2|]),
            eq (p![mix|t1^1|]) (q![mix|t1^1|]),
            eq (p![mix|t1^1,1|]) (q![mix|t1^1,1|]),
            eq (p![mix|t1^1,2|]) (q![mix|t1^1,2|])]
      S.fromList isCs `shouldBe` S.fromList cs
  describe "cLetBodyBase" $ do
    it "generates the correct constraints" $ do
      let (t1, t2) = ("t1", "t2")
      let q = defaultAnn pot 0 "Q" "" [(t1, treeT), (t2, treeT)]
      let p' = defaultAnn pot 1 "P'" "" []
      let r_ = emptyAnn pot 2 "R" "" [(t2, treeT)]
      let (r, isCs) = cLetBodyBase q r_ p'
      let cs = concat [
            eq (r!t2) (q!t2),
            eq (r![mix|2|]) (p'![mix|2|]),
            eq (r![mix|t2^1|]) (q![mix|t2^1|]),
            eq (r![mix|t2^1,1|]) (q![mix|t2^1,1|]),
            eq (r![mix|t2^1,2|]) (q![mix|t2^1,2|])]
      S.fromList isCs `shouldBe` S.fromList cs
  describe "cLetBinding" $ do
    it "generates the correct constraints" $ do
      let (t1, t2, e) = ("t1", "t2", "e")
      let q = defaultAnn pot 0 "Q" "" [(t1, treeT), (t2, treeT)]
      let p_ = emptyAnn pot 1 "P" "" [(t1, treeT)]
      let (p, isCs) = cLetBinding q p_ 
      let cs = concat [
            eq (p!t1) (q!t1),
            eq (p![mix|t1^1|]) (q![mix|t1^1|]),
            eq (p![mix|t1^1,1|]) (q![mix|t1^1,1|]),
            eq (p![mix|t1^1,2|]) (q![mix|t1^1,2|]),
            le (p![mix|2|]) (q![mix|2|])]
      S.fromList isCs `shouldBe` S.fromList cs
  describe "cLetBody" $ do
    it "generates the correct constraints" $ do
      let (t1, t2, e) = ("t1", "t2", "e")
      let x = "x"
      let q = defaultAnn pot 0 "Q" "" [(t1, treeT), (t2, treeT)]
      let p_ = emptyAnn pot 1 "P" "" [(t1, treeT)]
      let p' = defaultAnn pot 1 "P'" "" [(e, treeT)]
      let r_ = emptyAnn pot 2 "R" "" [(t2, treeT), (x, treeT)]
      let bdes = forAllCombinations pot q [t2] (_aRange, _bRange) x
      
      let ps_ = annArrayFromIdxs bdes "P" [(t1, treeT)]
      let ps'_ = annArrayFromIdxs bdes "P'" [(e, treeT)]
      
      let (p, pCs) = cLetBinding q p_
      let (ps, ps', cfCs) = cLetCf q ps_ ps'_ x ([t1], [t2]) bdes
      
      let (r, rCs) = cLetBody q r_ p p' ps' x bdes
      let cs = concat [
            eq (r!t2) (q!t2),
            eq (r!x) (p'!e),
            [Eq (r![mix|2|]) (Sum [p'![mix|2|], Minus (p![mix|2|]), q![mix|2|]])],
            eq (r![mix|t2^1|]) (q![mix|t2^1|]),
            eq (r![mix|t2^1,1|]) (ps'!![mix|t2^1,1|]![mix|1|]),
            eq (r![mix|t2^1,2|]) (ps'!![mix|t2^1,2|]![mix|2|]),
            eq (r![mix|x^1|]) (p'![mix|e^1|]),
            eq (r![mix|x^1,1|]) (p'![mix|e^1,1|]),
            eq (r![mix|x^1,2|]) (p'![mix|e^1,2|]),
            eq (r![mix|t2^1,x^1|]) (ps'!![mix|t2^1,x^1|]![mix|e^1|]),
            eq (r![mix|t2^1,x^1,1|]) (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]),
            eq (r![mix|t2^1,x^1,2|]) (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|])]
      S.fromList rCs `shouldBe` S.fromList cs
  describe "cLetCf" $ do
    it "generates the correct constraints" $ do
      let (t1, t2, e) = ("t1", "t2", "e")
      let x = "x"
      let q = defaultAnn pot 0 "Q" "" [(t1, treeT), (t2, treeT)]
      let p_ = emptyAnn pot 1 "P" "" [(t1, treeT)]
      let p' = defaultAnn pot 1 "P'" "" [(e, treeT)]
      let r_ = emptyAnn pot 2 "R" "" [(t2, treeT), (x, treeT)]
      let bdes = forAllCombinations pot q [t2] (_aRange, _bRange) x
      
      let ps_ = annArrayFromIdxs bdes "P" [(t1, treeT)]
      let ps'_ = annArrayFromIdxs bdes "P'" [(e, treeT)]
      
      let (p, pCs) = cLetBinding q p_
      let (ps, ps', cfCs) = cLetCf q ps_ ps'_ x ([t1], [t2]) bdes
      
      let cs = concat [
            eq (q![mix|t2^1,1|]) (sum [ps!![mix|t2^1,1|]![mix|1|],
                                        ps!![mix|t2^1,2|]![mix|1|],
                                        ps!![mix|t2^1,x^1|]![mix|1|],
                                        ps!![mix|t2^1,x^1,1|]![mix|1|],
                                        ps!![mix|t2^1,x^1,2|]![mix|1|]]),
            eq (q![mix|t2^1,2|]) (sum [ps!![mix|t2^1,1|]![mix|2|],
                                        ps!![mix|t2^1,2|]![mix|2|],
                                        ps!![mix|t2^1,x^1|]![mix|2|],
                                        ps!![mix|t2^1,x^1,1|]![mix|2|],
                                        ps!![mix|t2^1,x^1,2|]![mix|2|]]),
            eq (q![mix|t1^1,t2^1|]) (sum [
                                        ps!![mix|t2^1,1|]![mix|t1^1|],
                                        ps!![mix|t2^1,2|]![mix|t1^1|],
                                        ps!![mix|t2^1,x^1|]![mix|t1^1|],
                                        ps!![mix|t2^1,x^1,1|]![mix|t1^1|],
                                        ps!![mix|t2^1,x^1,2|]![mix|t1^1|]]),
            eq (q![mix|t1^1,t2^1,1|]) (sum [
                                        ps!![mix|t2^1,1|]![mix|t1^1,1|],
                                        ps!![mix|t2^1,2|]![mix|t1^1,1|],
                                          ps!![mix|t2^1,x^1|]![mix|t1^1,1|],
                                         ps!![mix|t2^1,x^1,1|]![mix|t1^1,1|],
                                         ps!![mix|t2^1,x^1,2|]![mix|t1^1,1|]]),
            eq (q![mix|t1^1,t2^1,2|]) (sum [
                                        ps!![mix|t2^1,1|]![mix|t1^1,2|],
                                        ps!![mix|t2^1,2|]![mix|t1^1,2|],
                                          ps!![mix|t2^1,x^1|]![mix|t1^1,2|],
                                         ps!![mix|t2^1,x^1,1|]![mix|t1^1,2|],
                                         ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]]),

            le (ps'!![mix|t2^1,1|]![mix|1|]) (sum [ps!![mix|t2^1,1|]![mix|1|],
                                                   ps!![mix|t2^1,1|]![mix|t1^1,1|],
                                                   ps!![mix|t2^1,1|]![mix|2|],
                                                   ps!![mix|t2^1,1|]![mix|t1^1,2|],
                                                   ps!![mix|t2^1,1|]![mix|t1^1|]]),
            zero (ps'!![mix|t2^1,1|]!?[mix|2|]),  
            zero (ps'!![mix|t2^1,1|]!?[mix|e^1|]),
            zero (ps'!![mix|t2^1,1|]!?[mix|e^1,1|]),
            zero (ps'!![mix|t2^1,1|]!?[mix|e^1,2|]),
            
            le (ps'!![mix|t2^1,2|]![mix|2|]) (sum [ps!![mix|t2^1,2|]![mix|1|],
                                                   ps!![mix|t2^1,2|]![mix|t1^1,1|],
                                                   ps!![mix|t2^1,2|]![mix|2|],
                                                   ps!![mix|t2^1,2|]![mix|t1^1,2|],
                                                   ps!![mix|t2^1,2|]![mix|t1^1|]]),
            zero (ps'!![mix|t2^1,2|]!?[mix|1|]),  
            zero (ps'!![mix|t2^1,2|]!?[mix|e^1|]),
            zero (ps'!![mix|t2^1,2|]!?[mix|e^1,1|]),
            zero (ps'!![mix|t2^1,2|]!?[mix|e^1,2|]),
            le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (sum [ps!![mix|t2^1,x^1|]![mix|1|],
                                                       ps!![mix|t2^1,x^1|]![mix|t1^1,1|],
                                                       ps!![mix|t2^1,x^1|]![mix|2|],
                                                       ps!![mix|t2^1,x^1|]![mix|t1^1,2|],
                                                       ps!![mix|t2^1,x^1|]![mix|t1^1|]]),
            zero (ps'!![mix|t2^1,x^1|]!?[mix|1|]),  
            zero (ps'!![mix|t2^1,x^1|]!?[mix|2|]),
            zero (ps'!![mix|t2^1,x^1|]!?[mix|e^1,1|]),
            zero (ps'!![mix|t2^1,x^1|]!?[mix|e^1,2|]),
            
            le (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]) (sum [ps!![mix|t2^1,x^1,1|]![mix|1|],
                                                         ps!![mix|t2^1,x^1,1|]![mix|t1^1,1|],
                                                         ps!![mix|t2^1,x^1,1|]![mix|2|],                                                                ps!![mix|t2^1,x^1,1|]![mix|t1^1,2|],
                                                         ps!![mix|t2^1,x^1,1|]![mix|t1^1|]]),
            zero (ps'!![mix|t2^1,x^1|]!?[mix|1|]),                
            zero (ps'!![mix|t2^1,x^1,1|]!?[mix|2|]),
            zero (ps'!![mix|t2^1,x^1,1|]!?[mix|e^1|]),
            zero (ps'!![mix|t2^1,x^1,1|]!?[mix|e^1,2|]),
            
            le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (sum [
                                                         ps!![mix|t2^1,x^1,2|]![mix|1|],
                                                         ps!![mix|t2^1,x^1,2|]![mix|t1^1,1|],
                                                         ps!![mix|t2^1,x^1,2|]![mix|2|],                                                                ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|],
                                                         ps!![mix|t2^1,x^1,2|]![mix|t1^1|]]),
            zero (ps'!![mix|t2^1,x^1|]!?[mix|1|]),                
            zero (ps'!![mix|t2^1,x^1,2|]!?[mix|2|]),
            zero (ps'!![mix|t2^1,x^1,2|]!?[mix|e^1,1|]),
            zero (ps'!![mix|t2^1,x^1,2|]!?[mix|e^1|]),

            impl (notZero (ps!![mix|t2^1,1|]![mix|1|])) (le (ps'!![mix|t2^1,1|]![mix|1|]) (ps!![mix|t2^1,1|]![mix|1|])),
            impl (notZero (ps!![mix|t2^1,1|]![mix|2|])) (le (ps'!![mix|t2^1,1|]![mix|1|]) (ps!![mix|t2^1,1|]![mix|2|])),
            impl (notZero (ps!![mix|t2^1,1|]![mix|t1^1|])) (le (ps'!![mix|t2^1,1|]![mix|1|]) (ps!![mix|t2^1,1|]![mix|t1^1|])),
            impl (notZero (ps!![mix|t2^1,1|]![mix|t1^1,1|])) (le (ps'!![mix|t2^1,1|]![mix|1|]) (ps!![mix|t2^1,1|]![mix|t1^1,1|])),
            impl (notZero (ps!![mix|t2^1,1|]![mix|t1^1,2|])) (le (ps'!![mix|t2^1,1|]![mix|1|]) (ps!![mix|t2^1,1|]![mix|t1^1,2|])),

            impl (notZero (ps!![mix|t2^1,2|]![mix|1|])) (le (ps'!![mix|t2^1,2|]![mix|2|]) (ps!![mix|t2^1,2|]![mix|1|])),
            impl (notZero (ps!![mix|t2^1,2|]![mix|2|])) (le (ps'!![mix|t2^1,2|]![mix|2|]) (ps!![mix|t2^1,2|]![mix|2|])),
            impl (notZero (ps!![mix|t2^1,2|]![mix|t1^1|])) (le (ps'!![mix|t2^1,2|]![mix|2|]) (ps!![mix|t2^1,2|]![mix|t1^1|])),
            impl (notZero (ps!![mix|t2^1,2|]![mix|t1^1,1|])) (le (ps'!![mix|t2^1,2|]![mix|2|]) (ps!![mix|t2^1,2|]![mix|t1^1,1|])),
            impl (notZero (ps!![mix|t2^1,2|]![mix|t1^1,2|])) (le (ps'!![mix|t2^1,2|]![mix|2|]) (ps!![mix|t2^1,2|]![mix|t1^1,2|])),

            impl (notZero (ps!![mix|t2^1,x^1|]![mix|1|])) (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|1|])),
            impl (notZero (ps!![mix|t2^1,x^1|]![mix|2|])) (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|2|])),
            impl (notZero (ps!![mix|t2^1,x^1|]![mix|t1^1|])) (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1|])),
            impl (notZero (ps!![mix|t2^1,x^1|]![mix|t1^1,1|])) (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1,1|])),
            impl (notZero (ps!![mix|t2^1,x^1|]![mix|t1^1,2|])) (le (ps'!![mix|t2^1,x^1|]![mix|e^1|]) (ps!![mix|t2^1,x^1|]![mix|t1^1,2|])),

            impl (notZero (ps!![mix|t2^1,x^1,1|]![mix|1|])) (le (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]) (ps!![mix|t2^1,x^1,1|]![mix|1|])),
            impl (notZero (ps!![mix|t2^1,x^1,1|]![mix|2|])) (le (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]) (ps!![mix|t2^1,x^1,1|]![mix|2|])),
            impl (notZero (ps!![mix|t2^1,x^1,1|]![mix|t1^1|])) (le (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]) (ps!![mix|t2^1,x^1,1|]![mix|t1^1|])),
            impl (notZero (ps!![mix|t2^1,x^1,1|]![mix|t1^1,1|])) (le (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]) (ps!![mix|t2^1,x^1,1|]![mix|t1^1,1|])),
            impl (notZero (ps!![mix|t2^1,x^1,1|]![mix|t1^1,2|])) (le (ps'!![mix|t2^1,x^1,1|]![mix|e^1,1|]) (ps!![mix|t2^1,x^1,1|]![mix|t1^1,2|])),

            impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|1|])) (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|1|])),
            impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|2|])) (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|2|])),
            impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1|])) (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1|])),
            impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1,1|])) (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1,1|])),
            impl (notZero (ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|])) (le (ps'!![mix|t2^1,x^1,2|]![mix|e^1,2|]) (ps!![mix|t2^1,x^1,2|]![mix|t1^1,2|]))
            ]
            

      let setIs = S.fromList cfCs
      let setShould = S.fromList cs
      setIs S.\\ setShould `shouldBe` S.empty
      --setShould S.\\ setIs `shouldBe` S.empty
      setIs `shouldBe` setShould
  describe "cWeakenVar" $ do
    it "generates the correct constraints" $ do
      let (x1, x2) = ("x1", "x2")
      let q = defaultAnn pot 0 "Q" "" [(x1, treeT), (x2, treeT)]
      let r_ = emptyAnn pot 1 "R" "" [(x2, treeT)]
      let (r,isCs) = cWeakenVar q r_
      let cs = concat [eq (r!x2) (q!x2),
                       eq (r![mix|2|]) (q![mix|2|]),
                       eq (r![mix|x2^1|]) (q![mix|x2^1|]),
                       eq (r![mix|x2^1,1|]) (q![mix|x2^1,1|]),
                       eq (r![mix|x2^1,2|]) (q![mix|x2^1,2|])]
      let setIs = S.fromList isCs
      let setShould = S.fromList cs
      setIs `shouldBe` setShould
