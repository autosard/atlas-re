module CostAnalysis.Weakening where

import Prelude hiding (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map(Map)
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
import Typing.Type

farkas :: ExpertKnowledge -> ProveMonad [Constraint]
farkas (ExpertKnowledge (as, bs) ps qs) = do
  let pTs = V.map snd ps
      qTs = V.map snd qs
  fs <- mapM (const freshVar) bs
  let fsPos = [ge f (ConstTerm 0) | f <- fs]
  let farkasA = [le (pTs V.! i) (sum (qTs V.! i:fas fs as i)) | i <- [0..length ps - 1]]
  let farkasB = [le (sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ concatMap concat [fsPos, farkasA, farkasB]
  where prods fs as = zipWith prod2 fs (map (ConstTerm . fromIntegral) as)
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])

ctxFarkas :: Set WeakenArg -> AnnCtx -> AnnCtx -> ProveMonad [Constraint]
ctxFarkas wArgs ps qs = do
  ks <- M.fromList <$> mapM go (M.toAscList ps)
  farkas =<< genInterPotKnowledge ks
  where go :: (Type, RsrcAnn) -> ProveMonad (Type, ExpertKnowledge)
        go (t, p) = do
          pot <- potForType t <$> use potentials
          let q = qs M.! t
          let m = genExpertKnowledge pot wArgs (p^.args) (p^.coeffs)
              ps = V.fromList [(idx, p!?idx) | idx <- S.toList (p^.coeffs)]
              qs = V.fromList [(idx, q!?idx) | idx <- S.toList (p^.coeffs)]
          return (t, ExpertKnowledge m ps qs)


genInterPotKnowledge :: Map Type ExpertKnowledge -> ProveMonad ExpertKnowledge
genInterPotKnowledge ks = do
  let ts = M.keys ks
  pots <- use potentials
  let as = V.fromList [ V.concat 
                        [ if rowT == colT then
                            let k = ks M.! colT in
                              fst (matrix k) V.! i
                          else 
                            genInterRow pots (ps V.! iP) rowT colT (V.map fst . cols $ ks M.! colT)
                        | colT <- ts]
                      | rowT <- ts,
                        let ps = V.map fst . rows $ ks M.! rowT,
                        (i, row) <- V.toList . V.indexed . fst . matrix $ ks M.! rowT,
                        let iP = case V.findIndex (== 1) row of
                                   Just i -> i
                                   Nothing -> error "no 1 in row."]
  let bs = concatMap (snd . matrix) $ M.elems ks
  let rows' = V.concat $ map rows $ M.elems ks
  let cols' = V.concat $ map cols $ M.elems ks
  return $ ExpertKnowledge (as, bs) rows' cols'

genInterRow :: Map Type (Potential, RsrcAnn) -> CoeffIdx -> Type -> Type -> V.Vector CoeffIdx -> V.Vector Int
genInterRow pots p rowT colT cols
  | p == constCoeff (potForType rowT pots) =
      let colConst = constCoeff (potForType colT pots) in
        case V.elemIndex colConst cols of
          Just j -> V.generate (length cols) (\i -> if i == j then 1 else 0)
  | otherwise = V.replicate (length cols) 0
  
-- interPotConsts :: AnnCtx -> AnnCtx -> ProveMonad [Constraint]
-- interPotConsts ps qs = do
--   pConsts <- mapM constCoeffForType $ M.assocs ps
--   qConsts <- mapM constCoeffForType $ M.assocs qs
--   let m = monoLattice (\_ _ _ -> True) [] (S.fromList (map fst pConsts))
--       ps = V.fromList (map snd pConsts)
--       qs = V.fromList (map snd qConsts)
--   let knowledge = ExpertKnowledge m ps qs  
--   farkas knowledge ps qs
--   where constCoeffForType :: (Type, RsrcAnn) -> ProveMonad (CoeffIdx, Term)
--         constCoeffForType (t, q) = do
--           pot <- potForType t <$> use potentials
--           let idx = constCoeff pot
--           return (idx, q!?idx)
          
coeffForLine :: V.Vector Int -> V.Vector CoeffIdx -> CoeffIdx
coeffForLine line coeffs = case V.findIndex (== 1) line of
  Just i -> coeffs V.! i
  Nothing -> error "coeff not in line."
        
merge :: [LeMatrix] -> LeMatrix
merge ks = let (vs1, vs2) = unzip ks in (V.concat vs1, concat vs2) 

type MonoLe = [Id] -> CoeffIdx -> CoeffIdx -> Bool
                                        
monoLattice :: MonoLe -> [Id] -> Set CoeffIdx -> LeMatrix
monoLattice monoLe args idxs = merge . catMaybes $
  [ compare idxP idxQ
  | idxP <- S.toList idxs,
    idxQ <- S.toList idxs,
    idxP /= idxQ]
  where compare :: CoeffIdx -> CoeffIdx -> Maybe LeMatrix
        compare f1 f2 = if monoLe args f1 f2 then
          let i = S.findIndex f1 idxs
              j = S.findIndex f2 idxs in
            Just (V.singleton $ V.fromList [if k == i then 1 else
                                 if k == j then -1 else 0
                              | k <- [0..length idxs-1]], [0])
            else Nothing


