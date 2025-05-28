{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.SumOfLogs.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id, infinity)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.Coeff
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Weakening
import CostAnalysis.Potential.SumOfLogs.Base(Args(..))


supportedArgs = S.fromList [Mono, L2xy]

genExpertKnowledge :: Args -> Set WeakenArg -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge (Args {logLemmaFactor = factor}) wArgs args idxs = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = monoLattice monoLe args idxs
        select L2xy = logLemma factor args idxs

-- \sum a_i * |x_i| + a_{n+1} <= \sum b_i * |y_i| b_{n+1}.
-- We know that arguments are trees, so we assume |x_i|,|y_i| >= 1. 
monoLe :: [Id] -> CoeffIdx -> CoeffIdx -> Bool
monoLe vars i@(Mixed _) j@(Mixed _) = sum (i `subtract` j) <= 0
  where subtract i j = let cD = fromIntegral $ constFactor i - constFactor j in
          cD : map (subFac i j) vars
        subFac i j x = let a = facForVar i x
                           b = facForVar j x in
                         if a - b <= 0 then fromIntegral $ a - b else infinity
monoLe vars i j@(Pure _) = justConst i && constFactor i == 2
monoLe _ _ _ = False

logLemma :: Rational -> [Id] -> Set CoeffIdx -> LeMatrix
logLemma factor args idxs = merge $ [(V.singleton (row x y xy), [0])
                             | (x,y,xy) <- idxTriples]
  where iConst = S.findIndex [mix|2|] idxs
        row idxX idxY idxXY = let iX = S.findIndex idxX idxs
                                  iY = S.findIndex idxY idxs
                                  iXY = S.findIndex idxXY idxs in
                    V.fromList [if k == iConst then factor else
                       if k == iX || k == iY then factor/2 else
                         if k == iXY then -factor else 0
                    | k <- [0..length idxs -1]]
        idxsMixed = S.toList $ S.filter (\i -> (not . isPure) i && (not . justConst) i) idxs
        idxTriples = [(idxX, idxY, idxXY)
                     | idxX <- idxsMixed,
                       idxY <- idxsMixed,
                       idxX `idxLessThen` idxY,
                       let idxXY = addIdxs idxX idxY,
                       S.member idxXY idxs]
        idxLessThen idxX idxY = xs < ys
          where xs = map (facForVar idxX) args ++ [constFactor idxX]
                ys = map (facForVar idxY) args ++ [constFactor idxY]
        
                              
