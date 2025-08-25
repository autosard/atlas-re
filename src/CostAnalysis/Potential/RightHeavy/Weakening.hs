{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.RightHeavy.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.Logarithm.Weakening(monoLe, logLemma2)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Weakening
import CostAnalysis.Annotation(Measure(..))
import CostAnalysis.Template(restrictFacs2)
import qualified CostAnalysis.Predicate as P
import CostAnalysis.Coeff (constFactor)


supportedArgs = S.fromList [Mono, L2xy]


genExpertKnowledge :: Set WeakenArg -> Set P.Predicate -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge wArgs preds args idxs = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        preds' = [ (x,y)
          | (P.Predicate m op x y [] _) <- S.toList preds,
            m == Weight,
            op == P.Le || op == P.Lt || op == P.Eq]
        select Mono = merge [
          monoLattice (monoLe preds') args idxs]
--          iversonLeOne args idxs]
        select L2xy = merge [
          logLemma2 preds' args idxs,
          logLemmaIverson args idxs]

iversonLeOne :: [Id] -> Set CoeffIdx -> LeMatrix
iversonLeOne args idxs = merge [(V.singleton (row i), [0])
                               | i <- restrictFacs2 $ S.toList idxs,
                                 (not . justConst) i]
  where iConst = S.findIndex [mix|2|] idxs
        row i = V.fromList $
                [if k == S.findIndex i idxs then 1 else
                    if k == iConst then -1 else 0
                | k <- [0..length idxs -1]]
        
logLemmaIverson :: [Id] -> Set CoeffIdx -> LeMatrix
logLemmaIverson args idxs = merge $ [(V.fromList (row i l r lr), [0,0])
                                    | (i,l,r,lr) <- lemmaCoeffs]
  where iConst = S.findIndex [mix|2|] idxs
        row idxILR idxL idxR idxLR
          = let iILR = S.findIndex idxILR idxs
                iL = S.findIndex idxL idxs
                iR = S.findIndex idxR idxs
                iLR = S.findIndex idxLR idxs
                lem = V.fromList $
                      [if k == iR || k == iConst then 1 else
                          if k == iLR || k == iILR then -1 else 0
                      | k <- [0..length idxs -1]]
                lemInv = V.fromList
                         [if k == iL || k == iILR then 1 else
                             if k == iLR then -1 else 0
                         | k <- [0..length idxs -1]] in
                                 [lem, lemInv]
        lemmaCoeffs = [(idxI, idxL, idxR, idxLR)
                      | idxI <- restrictFacs2 $ S.toList idxs,
                        let xs = varsForFac idxI [1,1],
                        let c = constFactor idxI,
                        let ys = varsForFac idxI [2,1],
                        let idxL = mixed . S.fromList $
                                     Const c:map (\x -> Arg x [1]) xs,
                        S.member idxL idxs,
                        let idxR = mixed $ S.fromList $ map (\x -> Arg x [1]) ys,
                        S.member idxR idxs,
                        let idxLR = addIdxs idxL idxR,
                        S.member idxLR idxs]

