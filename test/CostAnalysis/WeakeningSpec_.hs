{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.WeakeningSpec(spec) where

import Test.Hspec

import qualified Data.Set as S
import qualified Data.Map as M

import Primitive(Id)
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential.Log.Helper
import CostAnalysis.Deriv
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.ProveMonad
import CostAnalysis.Coeff
import Constants (treeT)
import CostAnalysis.Weakening
import CostAnalysis.Rules
import CostAnalysis.Constraint


import Control.Monad.RWS hiding (Sum)
import Control.Monad.Except
import Data.Ratio((%))


runProveMonad proof = result 
  where result = evalRWS rws env state
        rws = runExceptT $ proof
        env = ProofEnv pot M.empty
        state = ProofState M.empty 0 0 Nothing

spec :: Spec
spec = do
  describe "farkas" $ do
    it "generates the correct constraints for a small example." $ do
      let (x, y, z) = ("x", "y", "z")
      let proof = do
            let vars = [(x, treeT), (y, treeT), (z, treeT)]
            (RsrcAnn id _ _ _ _) <- emptyAnn "Q" "" vars
            let q = RsrcAnn id vars "Q" "" $ S.fromList [Pure x, [mix|x^1|], [mix|2|]]
            p <- enrichWithDefaults "P" "" q
            farkas pot (S.fromList [L2xy]) (_coeffs p) p q
      let (eitherCs, _) = runProveMonad proof
      let should = [
            Ge (VarTerm 0) (ConstTerm 0),
            Ge (VarTerm 1) (ConstTerm 0),
            Ge (VarTerm 2) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" (Pure x))) (Sum [CoeffTerm (Coeff 0 "Q" "" (Pure x))]),
            Le (CoeffTerm (Coeff 1 "P" "" (Pure y))) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" (Pure z))) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|y^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|z^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|y^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|z^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,y^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,z^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,y^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,z^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|y^1,z^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|y^1,z^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,y^1,z^1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,y^1,z^1,1|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,y^1,z^1,2|])) (ConstTerm 0),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|2|])) (Sum [CoeffTerm (Coeff 0 "Q" "" [mix|2|]), Prod [VarTerm 0, ConstTerm 2], Prod [VarTerm 1, ConstTerm 2],Prod [VarTerm 2, ConstTerm 2]]),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1|])) (Sum [CoeffTerm (Coeff 0 "Q" "" [mix|x^1|]), Prod [VarTerm 0, ConstTerm 1], Prod [VarTerm 1, ConstTerm 1]]),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|y^1|])) (Sum [Prod [VarTerm 0, ConstTerm 1], Prod [VarTerm 2, ConstTerm 1]]),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|z^1|])) (Sum [ Prod [VarTerm 1, ConstTerm 1], Prod [VarTerm 2, ConstTerm 1]]),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,y^1|])) (Sum [Prod [VarTerm 0, ConstTerm (-2)]]),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|x^1,z^1|])) (Sum [Prod [VarTerm 1, ConstTerm (-2)]]),
            Le (CoeffTerm (Coeff 1 "P" "" [mix|y^1,z^1|])) (Sum [Prod [VarTerm 2, ConstTerm (-2)]])
            ]
      case eitherCs of
        Right cs -> S.fromList cs `shouldBe` S.fromList should
        Left _ -> True `shouldBe` True     
          
             
            
            
    
