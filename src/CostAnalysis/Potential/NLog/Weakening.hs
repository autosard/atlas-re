module CostAnalysis.Potential.NLog.Weakening where

import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Coeff
import CostAnalysis.Potential
import CostAnalysis.Weakening

supportedArgs = S.fromList [Mono]

genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge wArgs args idxs = merge $ map select wArgs'
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = monoLattice monoLe args idxs
 

monoLe :: MonoLe
monoLe [x] i j = let (a,b) = facForVar2 i x
                     c = constFactor i
                     (a', b') = facForVar2 j x
                     c' = constFactor j in
                   monoLe' (a,b,c) (a',b',c')
monoLe [] i j = let c = constFactor i
                    c' = constFactor j in
                  monoLe' (0,0,c) (0,0,c')
monoLe xs _ _ = error $ "Weakening for linlog only supports univariate coefficients." 

monoLe' :: (Int, Int, Int) -> (Int, Int, Int) -> Bool
monoLe' (0,1,0) (0,1,1) = True -- log(n) <= log(n+1)
monoLe' (0,1,0) (1,0,2) = True -- log(n) <= n
monoLe' (0,1,0) (1,1,0) = True -- log(n) <= n*log(n)
monoLe' (1,1,0) (1,1,1) = True -- n*log(n) <= n*log(n+1)
monoLe' _ _ = False

