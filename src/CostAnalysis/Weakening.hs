module CostAnalysis.Weakening where

import Data.Set(Set)
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
      ps = V.map CoeffTerm $ V.fromList (getCoeffs p)
      qs = V.map CoeffTerm $ V.fromList (getCoeffs q)
  fs <- mapM (const (VarTerm <$> freshVar)) bs
  let fsPos = [Ge f (ConstTerm 0) | f <- fs]
  let farkasA = [Le (ps V.! i) (Sum (qs V.! i:fas fs as i)) | i <- [0..length ps - 1]]
  let farkasB = [Le (Sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ fsPos ++ farkasA ++ farkasB 
  where prods fs as = filter (\(Prod2 f (ConstTerm a)) -> a /= 0) (zipWith Prod2 fs (map (ConstTerm . fromIntegral) as))
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])
        
    
