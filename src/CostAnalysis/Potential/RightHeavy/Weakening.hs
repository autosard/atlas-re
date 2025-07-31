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
        select L2xy = logLemma2 preds' args idxs
