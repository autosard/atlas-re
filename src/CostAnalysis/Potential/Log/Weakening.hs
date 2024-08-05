{-# LANGUAGE QuasiQuotes #-}

module CostAnalysis.Potential.Log.Weakening where

import qualified Data.Vector as V
import Data.Set(Set)
import Data.Maybe(catMaybes)
import qualified Data.Set as S
import qualified Data.List as L
import Lens.Micro.Platform

import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Rules(WeakenArg(..))
import CostAnalysis.Potential(ExpertKnowledge)
import CostAnalysis.Coeff
import CostAnalysis.AnnIdxQuoter(mix)

supportedArgs = S.fromList [Mono, L2xy]

merge :: [ExpertKnowledge] -> ExpertKnowledge
merge ks = let (vs1, vs2) = unzip ks in (V.concat vs1, concat vs2)

genExpertKnowledge :: Args -> Set WeakenArg -> RsrcAnn -> RsrcAnn -> ExpertKnowledge
genExpertKnowledge potArgs wArgs p q | (q^.args) /= (p^.args) = error "Cannot generate export knowledge for annotations with differing arguments."
                            | otherwise
  = merge $ map select wArgs' 
  where wArgs' = S.toList $ S.intersection wArgs supportedArgs
        select Mono = monoLattice potArgs p q
        select L2xy = logLemma potArgs p q

monoLattice :: Args -> RsrcAnn -> RsrcAnn -> ExpertKnowledge
monoLattice potArgs p q = merge . catMaybes $
  [ compare idxP idxQ
  | idxP <- S.toList $ p^.coeffs,
    idxQ <- S.toList $ q^.coeffs,
    idxP /= idxQ]
  where iConst = S.findIndex [mix|2|] (p^.coeffs)
        compare :: CoeffIdx -> CoeffIdx -> Maybe ExpertKnowledge
        compare (Mixed f1) (Mixed f2) = if monoLe f1 f2 then
          let i = S.findIndex (Mixed f1) (p^.coeffs)
              j = S.findIndex (Mixed f2) (p^.coeffs) in
            Just (V.singleton $ V.fromList [if k == i then 1 else
                                 if k == j then -1 else 0
                              | k <- [0..length (p^.coeffs)-1]], [0])
            else Nothing
        compare _ _ = Nothing
  
monoLe :: Set Factor -> Set Factor -> Bool
monoLe s1 s2 = go (S.toAscList s1) (S.toAscList s2)
  where go :: [Factor] -> [Factor] -> Bool
        go [] ys = True
        go xs [] = False
        go ((Arg x a):xs) ((Const c):ys) = go (Arg x a:xs) ys
        go ((Arg x a):xs) ((Arg y b):ys) | x == y = a <= b && go xs ys
                                         | otherwise = go (Arg x a:xs) ys
        go ((Const c):xs) ((Const d):ys) = c <= d && go xs ys
        go ((Const c):xs) ((Arg y b):ys) = False

logLemma :: Args -> RsrcAnn -> RsrcAnn -> ExpertKnowledge
logLemma potArgs p q = merge $ [(V.singleton (row x y), [0])
                               | (x,y) <- varPairs]
  where iConst = S.findIndex [mix|2|] (p^.coeffs)
        row x y = let iX = S.findIndex [mix|x^1|] (p^.coeffs)
                      iY = S.findIndex [mix|y^1|] (p^.coeffs)
                      iXY = S.findIndex [mix|x^1,y^1|] (p^.coeffs) in
                    V.fromList [if k == iConst then 2 else
                       if k == iX || k == iY then 1 else
                         if k == iXY then -2 else 0
                    | k <- [0..length (p^.coeffs) -1]]
        varPairs = [(x,y) | (x:ys) <- L.tails (map fst (p^.args)), y <- ys]
