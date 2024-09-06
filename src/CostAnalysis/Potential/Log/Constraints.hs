{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Constraints where

import Prelude hiding (exp, (!!), sum)
import qualified Data.List as L
import qualified Data.Set as S
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
    concat [eqSum (q![mix|c|]) ([q'!?[mix|exp^a,b|]
                                | a <- [0..c],
                                  let b = c - a,
                                  a + b == c] ++ addRank)
                        | idx <- mixes q,
                          let c = constFactor idx,
                          let addRank = [q'!?exp | c == 2],
                          c >= 2]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=2) . map constFactor) (mixes q),
         idx <- mixes q',
         idx /= [mix|exp^1|], -- TODO this should not be necessary
         idxSum idx `S.notMember` qConsts]

  -- node
  | (length . _args $ q) == 2 && (length . _args $ q') == 1 =
    let [x1, x2] = annVars q in
      eq (q!?x1) (q'!?exp) 
      ++ eq (q!?x2) (q'!?exp)
      ++ eq (q!?[mix|x1^1|]) (q'!?exp)
      ++ eq (q!?[mix|x2^1|]) (q'!?exp)
      ++ concat [eq (q!idx) (q'!?[mix|exp^a,c|])
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
  where ys' = filter (\(x, t) -> bearesPotential t) ys

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
              a >= 0, b >= 0,
              let c = a + b,
              let xs = varsExcept idx [x],
              not (null xs && c == 1)]
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
-- tuple with one tree
cMatch' q r x [v] = extendAnn r $
  ((`eq` (q!x)) <$> def v)
  : [(`eq` (q!idx)) <$> def [mix|_xs,v^a,b|]
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
       onlyVarsOrConst idx xs]
  where xs = annVars p

cLetBodyBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyBase q r p' = extendAnn r $
  [(`eq` (q!y)) <$> def y | y <- ys]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVarsOrConst idx ys,
       not . justConst $ idx]
  ++ [(`eq` (p'!idx)) <$> def idx
     | idx <- mixes p',
       justConst idx]
  where ys = annVars r

cLetBinding :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBinding q p = extendAnn p $
  [(`eq` (q!x)) <$> def x  | x <- xs]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVarsOrConst idx xs,
       (not . justConst) idx]
  -- move const
  ++ [(`le` (q!?[mix|2|])) <$> def [mix|2|]]
  where xs = annVars p


cLetBody :: RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> AnnArray -> Id -> [CoeffIdx] -> (RsrcAnn, [Constraint])
cLetBody q r p p' ps' x bdes = extendAnn r $
  [(`eq` (q!y)) <$> def y | y <- ys]
  ++ [(`eq` (p'!("e" :: Id))) <$> def x]
  -- move const 
  ++ [(`eq` sum [sub [p'![mix|2|], p![mix|2|]], q!?[mix|2|]]) <$> def [mix|2|]]
  ++ [(`eq` (p'!pIdx)) <$> def [mix|x^d,e|]
     | pIdx <- mixes p',
       let d = facForVar pIdx exp,
       let e = constFactor pIdx,
       (d, e) /= (0,2)]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
--       annVars q /= ys || onlyVars idx ys,
       onlyVars idx ys]
  ++ [(`eq` (ps'!!bde![mix|exp^d,e|])) <$> def bde
     | bde <- bdes,
       let d = facForVar bde x,
--       annVars q == ys || d /= 0,
       -- d /= 0 || constFactor bde /= 0,
       let e = max 0 $ constFactor bde]
  where ys = L.delete x (annVars r)

cLetCf :: RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (AnnArray, AnnArray, [Constraint])
cLetCf q ps ps' x (gamma, delta) bdes = (psDefined, ps'Defined, psCs ++ ps'Cs ++ cs)
  where (psDefined, psCs) = extendAnns ps $
          [ eq (q!idx) . sum <$>
            sequence [defEntry bde pIdx
                     | bde <- bdes,
                       varsRestrict bde delta == varsRestrict idx delta,
                       let as = varsRestrict idx gamma,
                       let e = constFactor bde,
                       let ce = constFactor idx + max 0 (-e),
                       let pIdx = [mix|_as,ce|]]
          | idx <- mixes q,
            let c = constFactor idx,
            (not . null) (varsRestrict idx delta),
            (not . null) (varsRestrict idx gamma) || c /= 0]
            --not (onlyVarsOrConst idx gamma),
            --not (onlyVarsOrConst idx delta)]
--            (null gamma && c /= 0) || not (onlyVarsOrConst idx delta)]
            
        (ps'Defined, ps'Cs) = extendAnns ps' $
          [(`le` sum [p!ac
                     | let p = psDefined!!bde,
                       ac <- S.toList $ definedIdxs p]) <$> defEntry bde de
          | bde <- bdes,
            let d = facForVar bde x,
            let e = max 0 $ constFactor bde,
            let de = [mix|exp^d,e|]]
        cs = concat
             [impl (notZero (psDefined!!bde!idx)) (le (ps'Defined!!bde!de) (psDefined!!bde!idx))
             | bde <- bdes,
               idx <- mixes (psDefined!!bde),
               (not . null) (varsRestrict idx gamma) || constFactor idx /= 0,
               let d = facForVar bde x,
               let e = max 0 $ constFactor bde,
               let de = [mix|exp^d,e|]]


cWeakenVar :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cWeakenVar q r = let xs = annVars r in
  extendAnn r $
    [(`eq` (q!x)) <$> def x | x <- xs]
    ++ [(`eq` (q!idx)) <$> def idx
       | idx <- mixes q,
         onlyVarsOrConst idx xs]

