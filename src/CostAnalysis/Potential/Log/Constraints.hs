{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Constraints where

import Prelude hiding (exp, (!!), sum, or)
import qualified Data.List as L
import qualified Data.Set as S
import Lens.Micro.Platform

import Primitive(Id)
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import Data.List.Extra (groupSort)
import Ast
import qualified Data.Text as T


exp :: Id
exp = "e1"

cConst :: PositionedExpr -> RsrcAnn -> RsrcAnn -> [Constraint]
cConst (Leaf {}) q q'
  = concat [eqSum (q![mix|c|]) ([q'!?[mix|exp^a,b|]
                                | a <- [0..c],
                                  let b = c - a,
                                  a + b == c] ++ addRank)
           | idx <- mixes q,
             let c = constFactor idx,
             let addRank = [q'!?exp | c == 2],
             c >= 1]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=1) . map constFactor) (mixes q),
         idx <- mixes q',
         idxSum idx `S.notMember` qConsts]
cConst e@(Node {}) q q'
  = let [x1, x2] = annVars q in
      eq (q!?x1) (q'!?exp) 
      ++ eq (q!?x2) (q'!?exp)
      ++ eq (q!?[mix|x1^1|]) (q'!?exp)
      ++ eq (q!?[mix|x2^1|]) (q'!?exp)
      ++ concat [eq (q!idx) (q'!?[mix|exp^a,c|])
                | idx <- mixes q,
                  let a = facForVar idx x1,
                  a == facForVar idx x2,
                  let c = constFactor idx]
      ++ concat [zero (q'![mix|exp^a,c|]) 
                | idx <- mixes q',
                  let a = facForVar idx exp,
                  let c = constFactor idx,
                  [mix|x1^a,x2^a,c|] `S.notMember` (q^.coeffs)]
cConst (Ast.Const id _) q q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint])
-- leaf  
cMatch q p x [] = extendAnn p $
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
              let xs = varsExcept idx [x]]
              --not (null xs && c == 1)]
-- node
cMatch q r x [u, v] = extendAnn r $
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
cMatch q r x [v] = extendAnn r $
  ((`eq` (q!x)) <$> def v)
  : [(`eq` (q!idx)) <$> def [mix|_xs,v^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (annVars q)]
cMatch _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

cLetBodyMulti :: AnnArray -> Id -> [CoeffIdx] -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyMulti ps' x is r_ = extendAnn r_ $
  [(`eq` (ps'!!i![mix|exp^d,e|])) <$> def i
  | i <- is,
    let d = facForVar i x,
    let e = max 0 $ constFactor i]

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
