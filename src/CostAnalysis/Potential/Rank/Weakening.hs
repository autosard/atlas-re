{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Potential.Rank.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential.Logarithm.Weakening(monoLe)
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.Weakening
import CostAnalysis.Coeff

import qualified CostAnalysis.Predicate as P

supportedArgs = S.fromList [Mono]

genExpertKnowledge :: Set WeakenArg -> Set P.Predicate -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge wArgs preds args idxs = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = merge [
          monoLattice (monoLe []) args idxs,
          rankLeLog args idxs]

rankLeLog :: [Id] -> Set CoeffIdx -> LeMatrix
rankLeLog args idxs = merge [(V.singleton (row (Pure x) [mix|x^1|]), [0])
                            | x <- args,
                              S.member (Pure x) idxs,
                              S.member [mix|x^1|] idxs]
  where iConst = S.findIndex [mix|2|] idxs
        row idxRank idxLog =
          let iRank = S.findIndex idxRank idxs
              iLog = S.findIndex idxLog idxs in
            V.fromList $
            [if k == iRank then 1 else
                if k == iLog then -1 else 0
            | k <- [0..length idxs -1]]

