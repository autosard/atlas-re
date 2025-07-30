{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Potential.RightHeavy.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.Logarithm(monoLe)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Weakening
import CostAnalysis.Annotation(Measure(..))
import qualified CostAnalysis.Predicate as P


supportedArgs = S.fromList [Mono, L2xy]


genExpertKnowledge :: Set WeakenArg -> Set P.Predicate -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge wArgs preds args idxs = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        preds' = [ (x,y)
          | (P.Predicate m op x y [] _) <- S.toList preds,
            m == Weight,
            op == P.Le || op == P.Lt || op == P.Eq]
        select Mono = monoLattice (monoLe preds') args idxs
        select L2xy = logLemma preds' args idxs

logLemma :: [(Id, Id)] -> [Id] -> Set CoeffIdx -> LeMatrix
logLemma lePreds args idxs = merge $ [(V.singleton (row x xy), [0])
                                     | (x,xy) <- idxPairs]
  where iConst = S.findIndex [mix|2|] idxs
        row idxX idxXY = let iX = S.findIndex idxX idxs
                             iXY = S.findIndex idxXY idxs in
                    V.fromList [if k == iConst || k == iX then 1 else
                                   if k == iXY then -1 else 0
                               | k <- [0..length idxs -1]]
        idxPairs = [(idxX, idxXY)
                   | (x,y) <- lePreds,
                     let idxX = [mix|x^1|],
                     S.member idxX idxs,
                     let idxXY = [mix|x^1,y^1|],
                     S.member idxXY idxs]
