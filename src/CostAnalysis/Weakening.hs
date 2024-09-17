module CostAnalysis.Weakening where

import Prelude hiding (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Vector as V
import Lens.Micro.Platform

import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Potential
import CostAnalysis.ProveMonad
import CostAnalysis.Rules
import CostAnalysis.Coeff

farkas :: Potential -> Set WeakenArg -> Set CoeffIdx -> RsrcAnn -> RsrcAnn -> ProveMonad [Constraint]
farkas pot wArgs idxs p q = do
  let (as, bs) = genExpertKnowledge pot wArgs (map fst (p^.args)) idxs
      ps = V.fromList [p!?idx | idx <- S.toList idxs]
      qs = V.fromList [q!?idx | idx <- S.toList idxs]
  fs <- mapM (const freshVar) bs
  let fsPos = [ge f (ConstTerm 0) | f <- fs]
  let farkasA = [le (ps V.! i) (sum (qs V.! i:fas fs as i)) | i <- [0..length idxs - 1]]
  let farkasB = [le (sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ concatMap concat [fsPos, farkasA, farkasB]
  where prods fs as = zipWith prod2 fs (map (ConstTerm . fromIntegral) as)
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])
        
    
