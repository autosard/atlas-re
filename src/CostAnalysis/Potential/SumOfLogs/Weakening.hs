{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module CostAnalysis.Potential.SumOfLogs.Weakening where

import Prelude hiding (subtract)
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Primitive(Id, infinity)
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(LeMatrix)
import CostAnalysis.Coeff
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Weakening
import CostAnalysis.Annotation(Measure(..))
import CostAnalysis.Potential.SumOfLogs.Base(Args(..), LogLemmaCoeffs(..))
import CostAnalysis.Potential.Logarithm(monoLe)
import qualified CostAnalysis.Predicate as P
import Data.Maybe (fromMaybe)


supportedArgs = S.fromList [Mono, L2xy]


genExpertKnowledge :: Args -> Set WeakenArg -> Set P.Predicate -> [Id] -> Set CoeffIdx -> LeMatrix
genExpertKnowledge (Args {logLemmaInstance = llCoeffs}) wArgs preds args idxs = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        preds' = [ (x,y)
          | (P.Predicate m op x y [] _) <- S.toList preds,
            m == Weight,
            op == P.Le || op == P.Lt || op == P.Eq]
        select Mono = monoLattice (monoLe preds') args idxs
        select L2xy = logLemma llCoeffs args idxs


  
logLemma :: LogLemmaCoeffs -> [Id] -> Set CoeffIdx -> LeMatrix
logLemma (LogLemmaCoeffs a b c d) args idxs = merge $ [(V.singleton (row x y xy), [0])
                                                    | (x,y,xy) <- idxTriples]
  where iConst = S.findIndex [mix|2|] idxs
        row idxX idxY idxXY = let iX = S.findIndex idxX idxs
                                  iY = S.findIndex idxY idxs
                                  iXY = S.findIndex idxXY idxs in
                    V.fromList [if k == iConst then d else
                       if k == iX then a else
                         if k == iY then b else
                           if k == iXY then -c else 0
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
        
                              
