module CostAnalysis.Potential.NLog.Weakening where

import Data.Set(Set)
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Coeff
import CostAnalysis.Potential
import CostAnalysis.Weakening

supportedArgs = S.fromList [Mono]

genExpertKnowledge :: Set WeakenArg -> [Id] -> Set CoeffIdx -> ExpertKnowledge
genExpertKnowledge wArgs args idxs = merge $ map select wArgs'
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = monoLattice monoLe args idxs
 

monoLe :: MonoLe
monoLe [x] i j = monoLe' (facForVar3 i x) (facForVar3 j x)
monoLe xs _ _ = error "Weakening for linlog only supports univariate coefficients."

monoLe' :: (Int, Int, Int) -> (Int, Int, Int) -> Bool
monoLe' (0,0,1) (1,0,0) = True -- log(n+1) <= n
monoLe' (0,0,1) (1,0,1) = True -- log(n+1) <= n*log(n+1)
monoLe' (0,1,0) (0,0,1) = True -- log(n) <= log(n+1)
monoLe' (0,1,0) (1,0,0) = True -- log(n) <= n
monoLe' (0,1,0) (1,1,0) = True -- log(n) <= n*log(n)
monoLe' (1,1,0) (1,0,1) = True -- n*log(n) <= n*log(n+1)
monoLe' _ _ = False

