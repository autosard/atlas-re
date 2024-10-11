module CostAnalysis.Potential.NLog.Weakening where

import Data.Set(Set)
import qualified Data.Vector as V
import qualified Data.Set as S
import Data.Maybe(catMaybes)

import Primitive(Id, infinity)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Coeff
import CostAnalysis.Potential



supportedArgs = S.fromList [Mono]

merge :: [ExpertKnowledge] -> ExpertKnowledge
merge ks = let (vs1, vs2) = unzip ks in (V.concat vs1, concat vs2)

-- genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> ExpertKnowledge
-- genExpertKnowledge wArgs args idxs = (V.empty, [])

genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> ExpertKnowledge
genExpertKnowledge wArgs args idxs = merge $ map select wArgs'
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = monoLattice args idxs
 
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

monoLe :: [Id] -> CoeffIdx -> CoeffIdx -> Bool
monoLe [x] i j = monoLe' (facForVar3 i x) (facForVar3 j x)
monoLe xs _ _ = error "Weakening for linlog only supports univariate coefficients."

monoLe' :: (Int, Int, Int) -> (Int, Int, Int) -> Bool
monoLe' (0,0,1) (1,0,0) = True -- log(n+1) <= n
monoLe' (0,0,1) (1,0,1) = True -- log(n+1) <= n*log(n+1)
monoLe' (0,1,0) (0,0,1) = True -- log(n) <= log(n+1)
monoLe' (0,1,0) (1,0,0) = True -- log(n) <= n
monoLe' (0,1,0) (1,1,0) = True -- log(n) <= n*log(n)
monoLe' (1,1,0) (1,0,1) = True -- n*log(n) <= n*log(n+1)
-- monoLe' (0,1,0) (1,0,1) = True -- log(n) <= n*log(n+1)
monoLe' _ _ = False

  -- where subtract i j = let cD = fromIntegral $ constFactor i - constFactor j in
  --         cD : map (subFac i j) vars
  --       subFac i j x = let (a1, b1, c1) = facForVar3 i x
  --                          (a2, b2, c2) = facForVar3 j x
  --                          s1 = if a1 - a2 <= 0 then fromIntegral $ a1 - a2 else infinity
  --                          bc = (b1 + c1) - (b2 + c2)
  --                          s2 = if bc <= 0 then fromIntegral bc else infinity in
  --                         -- c2 = if a2 - b2 <= 0 then fromIntegral $ a2 - b2 else infinity in
  --                        s1 + s2

