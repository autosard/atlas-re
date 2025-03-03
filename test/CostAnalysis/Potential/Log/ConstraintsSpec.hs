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
import CostAnalysis.Potential(defaultAnn, emptyAnn, letCfIdxs)
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
      let q' = defaultAnn pot 1 "Q'" "" ["e1"]
      let expr = ConstAnn posAnn "leaf" [] :: PositionedExpr
      let e = ("e1" :: Id)
      let should = 
            eqSum (q![mix|2|]) [q'![mix|2|], q'![mix|e^1,1|], q'!e] ++
            zero (q'![mix|e^1,2|])
      let cs = cConst expr q (trace (show q') q')
      S.fromList cs `shouldBe` S.fromList should

    it "generates the correct constraints for the node case" $ do
      let [x1, x2] = ["x1", "x2"]
      let e = "e1"
      let expr = ConstAnn posAnn "node" [VarAnn posAnn x1, VarAnn posAnn "v", VarAnn posAnn x2] :: PositionedExpr
      let q = defaultAnn pot 0 "Q" "" [x1, x2]
      let q' = defaultAnn pot 1 "Q'" "" [e]
      let should = concat [eq (q!x1) (q'!e),
                    eq (q!x2) (q'!e),
                    eq (q!["x1"^1]) (q'!e),
                    eq (q!["x2"^1]) (q'!e),
                    eq (q![Const 2]) (q'![Const 2]),
                    eq (q!["x1"^1, "x2"^1]) (q'![e^1]),
                    eq (q!["x1"^1, "x2"^1, Const 1]) (q'![e^1, Const 1]),
                    eq (q!["x1"^1, "x2"^1, Const 2]) (q'![e^1, Const 2])]
      let cs = cConst expr q q' 
      S.fromList cs `shouldBe` S.fromList should
 
  describe "cMatch" $ do
    it "generates the correct constraints for the leaf case" $ do
      let (x1, x2) = ("x1", "x2") 
      let q = defaultAnn pot 0 "Q" "" [x1, x2]
      let p = emptyAnn pot 1 "P" "" [x1]
      
      let (pDef, isCs) = cMatch q p x2 []
      let cs = concat [eq (pDef!x1) (q!x1) ,
                    eqSum (pDef![Const 1]) [q![mix|x2^1|]],
                    eqSum (pDef![Const 2]) [q!x2,q![mix|x2^1,1|],q![mix|2|]],
                    eqSum (pDef![Const 3]) [q![mix|x2^1,2|]],
                    eqSum (pDef!["x1"^1]) [q!["x1"^1]],
                    eqSum (pDef![mix|x1^1,2|]) [q![mix|x1^1,x2^1,1|], q![mix|x1^1,2|]],
                    eqSum (pDef!["x1"^1,Const 1]) [q!["x1"^1, Const 1],q![mix|x1^1,x2^1|]],
                    eqSum (pDef!["x1"^1,Const 3]) [q![mix|x1^1,x2^1,2|]]]
                  
      let pShould = RsrcAnn 1 [x1] "P" "" $ S.fromList [
            Pure x1,
            [mix|1|],
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
      let q = defaultAnn pot 0 "Q" "" [t]
      let r_ = emptyAnn pot 1 "R" "" [u, v]
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
  describe "cLetCf" $ do
    it "generates the correct constraints" $ do
      let (t1, t2, e) = ("t1", "t2", "e1")
      let x = "x"
      let q = defaultAnn pot 0 "Q" "" [t1, t2]
      let p_ = emptyAnn pot 1 "P" "" [t1]
      let p' = defaultAnn pot 1 "P'" "" [e]
      let r_ = emptyAnn pot 2 "R" "" [t2, x]
      let bdes = letCfIdxs pot q [t2] (_aRange, _bRange) x
      
      let ps_ = annArrayFromIdxs bdes "P" [t1]
      let ps'_ = annArrayFromIdxs bdes "P'" [e]
      
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
      setIs `shouldBe` setShould

-- TODO cLetBodyMulti
