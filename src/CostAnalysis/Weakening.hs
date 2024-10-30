module CostAnalysis.Weakening where

import Prelude hiding (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector as V
import Lens.Micro.Platform
import Data.Maybe(catMaybes)

import Primitive(Id)
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Potential
import CostAnalysis.ProveMonad
import CostAnalysis.Rules
import CostAnalysis.Coeff
import Control.Monad.Extra (concatMapM)

farkas :: Potential -> Set WeakenArg -> Set CoeffIdx -> RsrcAnn -> RsrcAnn -> ProveMonad [Constraint]
farkas pot wArgs idxs p q = do
  let (as, bs) = genExpertKnowledge pot wArgs (p^.args) idxs
      ps = V.fromList [p!?idx | idx <- S.toList idxs]
      qs = V.fromList [q!?idx | idx <- S.toList idxs]
  fs <- mapM (const freshVar) bs
  let fsPos = [ge f (ConstTerm 0) | f <- fs]
  let farkasA = [le (ps V.! i) (sum (qs V.! i:fas fs as i)) | i <- [0..length idxs - 1]]
  let farkasB = [le (sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ concatMap concat [fsPos, farkasA, farkasB]
  where prods fs as = zipWith prod2 fs (map (ConstTerm . fromIntegral) as)
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])

ctxFarkas :: Set WeakenArg -> AnnCtx -> AnnCtx -> ProveMonad [Constraint]
ctxFarkas wArgs ps qs = concatMapM go $ M.toAscList ps
  where go (t, p) = do
          pot <- potForType t <$> use potentials
          let q = qs M.! t
          farkas pot wArgs (p^.coeffs) p q
        
merge :: [ExpertKnowledge] -> ExpertKnowledge
merge ks = let (vs1, vs2) = unzip ks in (V.concat vs1, concat vs2)

type MonoLe = [Id] -> CoeffIdx -> CoeffIdx -> Bool
                                        
monoLattice :: MonoLe -> [Id] -> Set CoeffIdx -> ExpertKnowledge
monoLattice monoLe args idxs = merge . catMaybes $
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

