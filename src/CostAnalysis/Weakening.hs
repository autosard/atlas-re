module CostAnalysis.Weakening where

import Prelude hiding (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Vector as V

import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Potential
import CostAnalysis.ProveMonad
import CostAnalysis.Rules

-- | @'weaken' q q' p p'@
weaken :: Potential -> Set WeakenArg -> RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> ProveMonad [Constraint]
weaken pot args q q' p p' = (++)
  <$> farkas pot args p q -- p <= q
  <*> farkas pot args q' p' -- q' <= p'

farkas :: Potential -> Set WeakenArg -> RsrcAnn -> RsrcAnn -> ProveMonad [Constraint]
farkas pot args p q = do
  let (as, bs) = genExpertKnowledge pot args p q
      ps = V.fromList [p!idx | idx <- S.toList $ definedIdxs p]
      qs = V.fromList [q!idx | idx <- S.toList $ definedIdxs q]
  fs <- mapM (const freshVar) bs
  let fsPos = [ge f (ConstTerm 0) | f <- fs]
  let farkasA = [le (ps V.! i) (sum (qs V.! i:fas fs as i)) | i <- [0..length ps - 1]]
  let farkasB = [le (sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ concatMap concat [fsPos, farkasA, farkasB]
  where prods fs as = zipWith prod2 fs (map (ConstTerm . fromIntegral) as)
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])
        
    
