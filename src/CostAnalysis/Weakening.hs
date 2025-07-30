module CostAnalysis.Weakening where

import Prelude hiding (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Vector as V
import Lens.Micro.Platform
import Data.Maybe(catMaybes, isJust, fromJust)

import Primitive(Id)
import CostAnalysis.Annotation(FreeAnn, Ann)
import CostAnalysis.Template(FreeTemplate,
                             Template,
                            (!?), (!), idxs, args,
                            ftCoeffs)
                            
import CostAnalysis.Constraint
import CostAnalysis.Potential
import CostAnalysis.ProveMonad
import CostAnalysis.Rules
import CostAnalysis.Coeff
import Typing.Type
import CostAnalysis.Predicate (Predicate)

farkas :: ExpertKnowledge -> ProveMonad [Constraint]
farkas (ExpertKnowledge (as, bs) ps qs) = do
  let pTs = V.map snd ps
      qTs = V.map snd qs
  fs <- mapM (const freshVar) bs
  let fsPos = [ge f (ConstTerm 0) | f <- fs]
  let farkasA = [le (pTs V.! i) (sum (qTs V.! i:fas fs as i)) | i <- [0..length ps - 1]]
  let farkasB = [le (sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ concatMap concat [fsPos, farkasA, farkasB]
  where prods fs as = zipWith prod2 fs (map ConstTerm as)
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])

annFarkas :: (Template a, Template b) => Set WeakenArg -> Set Predicate -> Ann a -> Ann b -> ProveMonad [Constraint]
annFarkas wArgs preds ps qs = do
  ks <- M.fromList <$> mapM go (M.toAscList ps)
  farkas =<< genInterPotKnowledge ks
  where go :: (Template a) => (Type, a) -> ProveMonad (Type, ExpertKnowledge)
        go (t, p) = do
          pot <- potForType t 
          let q = qs M.! t
          let m = genExpertKnowledge pot wArgs preds (args p) (idxs p)
              ps = V.fromList [(idx, p!?idx) | idx <- S.toList (idxs p)]
              qs = V.fromList [(idx, q!?idx) | idx <- S.toList (idxs p)]
          return (t, ExpertKnowledge m ps qs)


genInterPotKnowledge :: Map Type ExpertKnowledge -> ProveMonad ExpertKnowledge
genInterPotKnowledge ks = do
  let ts = M.keys ks
  pots <- use potentials
  let cols' = V.concat $ map cols $ M.elems ks
  let rows' = V.concat $ map rows $ M.elems ks
  
  let as = V.fromList $ [ V.concat 
                          [ if rowT == colT then
                              let k = ks M.! colT in
                                fst (matrix k) V.! i
                            else
                              V.replicate (length (cols $ ks M.! colT)) 0
                          | colT <- ts]
                        | rowT <- ts,
                          let ps = V.map fst . rows $ ks M.! rowT,
                              (i, _) <- V.toList . V.indexed . fst . matrix $ ks M.! rowT]

  asInter <- interCoeffsEqual ks ts (Just . oneCoeff)
  let bs = concatMap (snd . matrix) $ M.elems ks 
  return $ ExpertKnowledge (V.concat [as, asInter], bs ++ replicate (length asInter) 0) rows' cols'

interCoeffsEqual :: Map Type ExpertKnowledge -> [Type] -> (Potential -> Maybe CoeffIdx) -> ProveMonad (V.Vector (V.Vector Rational))
interCoeffsEqual ks ts coeff = do
  pots <- M.fromList <$> mapM (\t -> do p <- potForType t
                                        return (t, p)) ts
  return $ V.fromList [
    V.concat $ map (buildSegment pots tQ tP) ts
    | tP <- ts,
      let potP = pots M.! tP,
      isJust $ coeff potP,
      let coeffP = fromJust $ coeff potP,
      isJust $ V.elemIndex coeffP (V.map fst $ cols $ ks M.! tP),
      tQ <- ts,
      let potQ = pots M.! tQ,
      isJust $ coeff potQ,
      let coeffQ = fromJust $ coeff potQ,
      isJust $ V.elemIndex coeffQ (V.map fst $ cols $ ks M.! tQ),    
      tP /= tQ]
    where buildSegment pots tP tQ t | t == tP
              = let coeffP = fromJust $ coeff (pots M.! tP) in
                singletonSegment coeffP (cols $ ks M.! tP) 1
                | t == tQ
              = let coeffQ = fromJust $ coeff (pots M.! tQ) in
                singletonSegment coeffQ (cols $ ks M.! tQ) (-1)
                | otherwise = V.replicate (length (cols $ ks M.! t)) 0
          singletonSegment idx cols x = case V.elemIndex idx (V.map fst cols) of
              Just j -> V.generate (V.length cols) (\i -> if i == j then x else 0)

-- genInterRow :: Map Type (Potential, FreeTemplate) -> CoeffIdx -> Type -> Type -> V.Vector CoeffIdx -> V.Vector Int
-- genInterRow pots p rowT colT cols
--   | p == oneCoeff (potForType rowT pots) =
--       let colConst = oneCoeff (potForType colT pots) in
--         case V.elemIndex colConst cols of
--           Just j -> V.generate (length cols) (\i -> if i == j then 1 else 0)
--   | otherwise = V.replicate (length cols) 0
          
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

monoShift :: MonoFn -> [Id] -> Int -> Potential -> FreeTemplate -> FreeTemplate -> Maybe [Constraint]
monoShift fn xs c pot p q = do
  idxFn <- monoFnCoeff pot fn xs 0
  idxFnShift <- monoFnCoeff pot fn xs c
  return $
    eq (q!?idxFnShift) (p!idxFn)
    ++ eq (q!?oneCoeff pot) (p!oneCoeff pot)
    ++ concat [ zero (p!idx)
              | idx <- S.toList $ idxs p,
                idx /= idxFn,
                idx /= oneCoeff pot]
    ++ concat [ zero (q!idx)
              | idx <- S.toList $ idxs q,
                idx /= idxFnShift,
                idx /= oneCoeff pot]


    
    
  
