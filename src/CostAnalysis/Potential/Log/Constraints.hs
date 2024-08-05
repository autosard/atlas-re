{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Constraints where

import Prelude hiding (exp, (!!), sum)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set(Set)
import Lens.Micro.Platform

import Primitive(Id)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import Typing.Type
import CostAnalysis.Coeff
import Data.List.Extra (groupSort)


exp :: Id
exp = "e"

cConst :: RsrcAnn -> RsrcAnn -> [Constraint]
cConst q q'
  -- leaf 
  | (null . _args $ q) && (length . _args $ q') == 1 =
    eqSum (q!?[mix|2|]) [q'!?exp, q'!?[mix|2|]] 
    ++ concat [eqSum (q![mix|c|]) [q'!?[mix|exp^a,b|]
                            | a <- [0..c],
                              let b = c - a,
                              a + b == c]
                        | idx <- mixes q,
                          let c = constFactor idx,
                          c > 2]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=2) . map constFactor) (mixes q),
         idx <- mixes q',
         idxSum idx `S.notMember` qConsts]

  -- node
  | (length . _args $ q) == 2 && (length . _args $ q') == 1 =
    let [x1, x2] = annVars q in
      eq (q!?x1) (q'!?exp) 
      ++ eq (q!?x2) (q'!?exp) 
      ++ eq (q!?[mix|x1^1|]) (q'!?exp) 
      ++ eq (q!?[mix|x2^1|]) (q'!?exp) 
      ++ concat [eq (q!?[mix|x1^a,x2^a,c|]) (q'!?[mix|exp^a,c|])
                | idx <- mixes q,
                  let a = facForVar idx x1,
                  a == facForVar idx x2,
                  let c = constFactor idx]
      ++ concat [zero (q![mix|x1^x,x2^y,c|]) 
                | idx <- mixes q,
                  let x = facForVar idx x1,
                  let y = facForVar idx x2,
                  let c = constFactor idx,
                  x /= y,
                  x + y + c > 1]
      ++ concat [zero (q'![mix|exp^a,c|]) 
                | idx <- mixes q',
                  let a = facForVar idx exp,
                  let c = constFactor idx,
                  [mix|x1^a,x2^a,c|] `S.notMember` (q^.coeffs)]
  | otherwise = error $ show q ++ show q'
      

cMatch :: RsrcAnn -> RsrcAnn -> Id -> [(Id, Type)] -> (RsrcAnn, [Constraint])
cMatch q p x ys = cMatch' q p x (map fst ys')
  where ys' = filter (\(x, t) -> matchesTypes t types) ys

cMatch' :: RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint])
-- leaf  
cMatch' q p x [] = extendAnn p $
  [(`eq` (q!y)) <$> def y | y <- L.delete x (annVars q)]
  ++ [(`eqSum` qs) <$> def [mix|_xs, c|]
     | ((xs, c), qs) <- sums]
  where sums = groupSort $
          ((S.empty, 2), q!x)
          : [((xs, c), q!idx) 
            | idx <- mixes q,
              let a = facForVar idx x,
              let b = constFactor idx,
              a > 0, b > 0,
              let c = a + b,
              c /= 2,
              let xs = varsExcept idx [x]]
-- node
cMatch' q r x [u, v] = extendAnn r $
  [(`eq` (q!x)) <$> def u,
   (`eq` (q!x)) <$> def v,
   (`eq` (q!x)) <$> def [mix|u^1|],
   (`eq` (q!x)) <$> def [mix|v^1|]]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,u^a,v^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (annVars q)]
cMatch' _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

cLetBindingBase :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBindingBase q p = extendAnn p $
  [(`eq` (q!x)) <$> def x  | x <- xs]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx (S.fromList xs)]
  where xs = annVars p

cLetBodyBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyBase q r p' = extendAnn r $
  [(`eq` (q!y)) <$> def y | y <- ys]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx (S.fromList ys),
       (not . justConst) idx]
  ++ [(`eq` (p'!idx)) <$> def idx
     | idx <- mixes p',
       onlyVars idx S.empty]
  where ys = annVars r

cLetBinding :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBinding q p = extendAnn p $
  [(`eq` (q!x)) <$> def x  | x <- xs]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx (S.fromList xs),
       (not . justConst) idx]
  -- move const
  ++ [(`le` (q![mix|2|])) <$> def [mix|2|]]
  where xs = annVars p


cLetBody :: RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> AnnArray -> Id -> [Set Factor] -> (RsrcAnn, [Constraint])
cLetBody q r p p' ps' x bdes = extendAnn r $
  [(`eq` (q!y)) <$> def y | y <- ys]
  ++ [(`eq` (p'!("e" :: Id))) <$> def x]
  -- move const 
  ++ [(`eq` sum [sub [p'![mix|2|], p![mix|2|]], q![mix|2|]]) <$> def [mix|2|]]
  ++ [(`eq` (p'!pIdx)) <$> def [mix|x^d,e|]
     | pIdx <- mixes p',
       let d = facForVar pIdx x,
       let e = constFactor pIdx]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx (S.fromList ys),
       (not . justConst) idx]
  ++ [(`eq` (ps'!!bde![mix|x^d,e|])) <$> def idx
     | bde <- bdes,
       let idx = Mixed bde,
       let d = facForVar idx x,
       let e = max 0 $ constFactor idx]
  where ys = L.delete x (annVars r)

cLetCf :: RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) -> [Set Factor] -> (AnnArray, AnnArray, [Constraint])
cLetCf q ps ps' x (gamma, delta) bdes = (psDefined, ps'Defined, psCs ++ ps'Cs ++ cs)
  where (psDefined, psCs) = extendAnns ps $
          [ eq (q!idx) . sum <$>
            sequence [defEntry bde pIdx
                     | bde <- bdes,
                       let bs = varsExcept (Mixed bde) [x],
                       bs == varsExcept idx gamma,
                       let as = varsExcept idx delta,
                       let e = constFactor (Mixed bde),
                       let c = constFactor idx + max 0 (-e),
                       let pIdx = [mix|_as,c|]]
          | idx <- mixes q,
            not $ onlyVars idx (S.fromList gamma),
            not $ onlyVars idx (S.fromList delta),
            not $ onlyVars idx (S.singleton x)]
        (ps'Defined, ps'Cs) = extendAnns ps' $
          [(`le` sum [p!ac
                     | let p = psDefined!!bde,
                       ac <- S.toList $ definedIdxs p]) <$> defEntry bde de
          | bde <- bdes,
            let d = varsExcept (Mixed bde) delta,
            let e = max 0 $ constFactor (Mixed bde),
            let de = [mix|_d,e|]]
        cs = concat
             [impl (zero (psDefined!!bde!idx)) (le (ps'Defined!!bde!de) (ps!!bde!idx))
             | bde <- bdes,
               idx <- mixes (psDefined!!bde),
               (not . justConst) idx,
               let d = varsExcept (Mixed bde) delta,
               let e = max 0 $ constFactor (Mixed bde),
               let de = [mix|_d,e|]]


cWeakenVar :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cWeakenVar q r = let xs = annVars r in
  extendAnn r $
    [(`eq` (q!x)) <$> def x | x <- xs]
    ++ [(`eq` (q!idx)) <$> def idx
       | idx <- mixes q,
         onlyVars idx (S.fromList xs)]

