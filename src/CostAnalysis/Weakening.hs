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
      ps = V.fromList (getCoeffs p)
      qs = V.fromList (getCoeffs q)
  fs <- mapM (const freshPosVar) bs
  let farkasA = [FarkasA (ps V.! i) (prods fs ([row V.! i | row <- V.toList as])) (qs V.! i) | i <- [0..length ps - 1]]
  return $ if bs == replicate (length bs) 0 then farkasA else FarkasB (zip fs bs):farkasA 
  where prods fs as = filter (\(f, a) -> a /= 0) (zip fs as)
    
