{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.Log.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import Data.Maybe(catMaybes)
import qualified Data.Set as S

import Primitive(Id, infinity)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(ExpertKnowledge)
import CostAnalysis.Coeff
import CostAnalysis.AnnIdxQuoter(mix)


import CostAnalysis.RsrcAnn (isPure)

supportedArgs = S.fromList [Mono, L2xy]

merge :: [ExpertKnowledge] -> ExpertKnowledge
merge ks = let (vs1, vs2) = unzip ks in (V.concat vs1, concat vs2)

genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> ExpertKnowledge
genExpertKnowledge wArgs args idxs = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = monoLattice args idxs
        select L2xy = logLemma args idxs

monoLattice :: [Id] -> Set CoeffIdx -> ExpertKnowledge
monoLattice args idxs = merge . catMaybes $
  [ compare idxP idxQ
  | idxP <- S.toList idxs,
    idxQ <- S.toList idxs,
    idxP /= idxQ]
  where compare :: CoeffIdx -> CoeffIdx -> Maybe ExpertKnowledge
        compare (Mixed f1) (Mixed f2) = if monoLe args (Mixed f1) (Mixed f2) then
          let i = S.findIndex (Mixed f1) idxs
              j = S.findIndex (Mixed f2) idxs in
            Just (V.singleton $ V.fromList [if k == i then 1 else
                                 if k == j then -1 else 0
                              | k <- [0..length idxs-1]], [0])
            else Nothing
        compare _ _ = Nothing


-- \sum a_i * |x_i| + a_{n+1} <= \sum b_i * |y_i| b_{n+1}.
-- We know that arguments are trees, so we assume |x_i|,|y_i| >= 1. 
monoLe :: [Id] -> CoeffIdx -> CoeffIdx -> Bool
monoLe vars i j = sum (i `subtract` j) <= 0
  where subtract i j = let cD = fromIntegral $ constFactor i - constFactor j in
          cD : map (subFac i j) vars
        subFac i j x = let a = facForVar i x
                           b = facForVar j x in
                         if a - b <= 0 then fromIntegral $ a - b else infinity


logLemma :: [Id] -> Set CoeffIdx -> ExpertKnowledge
logLemma args idxs = merge $ [(V.singleton (row x y xy), [0])
                             | (x,y,xy) <- idxTriples]
  where iConst = S.findIndex [mix|2|] idxs
        row idxX idxY idxXY = let iX = S.findIndex idxX idxs
                                  iY = S.findIndex idxY idxs
                                  iXY = S.findIndex idxXY idxs in
                    V.fromList [if k == iConst then 2 else
                       if k == iX || k == iY then 1 else
                         if k == iXY then -2 else 0
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
        
                              
