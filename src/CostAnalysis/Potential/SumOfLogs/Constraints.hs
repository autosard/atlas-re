{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.SumOfLogs.Constraints where

import Prelude hiding (exp, (!!), sum, or)
import qualified Data.List as L
import qualified Data.Set as S
import Lens.Micro.Platform

import Primitive(Id)
import CostAnalysis.Template hiding (sum)
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.SumOfLogs.Base(Args(..))
import Data.List.Extra (groupSort)
import Ast
import qualified Data.Text as T


exp :: Id
exp = "e1"

cConst :: Args -> PositionedExpr -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst _ (Leaf {}) (q, _) q'
  = concat [eqSum (q![mix|c|]) ([q'!?[mix|exp^a,b|]
                                | a <- [0..c],
                                  let b = c - a,
                                  a + b == c] ++ addRank)
           | idx <- mixes q,
             let c = constFactor idx,
             let addRank = [q'!?exp | c == 2],
             c >= 2]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=1) . map constFactor) (mixes q),
         idx <- mixes q',
         idxSum idx >= 2,
         idxSum idx `S.notMember` qConsts]
cConst (Args {logL=cL, logR=cR, logLR=cLR}) e@(Node (Var x1) _ (Var x2)) (q, qe) q'
  = 
      eq (q!?x1) (q'!?exp) 
      ++ eq (q!?x2) (q'!?exp)
      ++ eq (q!?[mix|x1^1|]) (prod [ConstTerm cL, q'!?exp])
      ++ eq (q!?[mix|x2^1|]) (prod [ConstTerm cR, q'!?exp])
      ++ eq (sum [qe!?[mix|exp^1|], q!?[mix|x1^1,x2^1|]]) (sum [
                                                             prod [ConstTerm cLR, q'!?exp],
                                                             q'!?[mix|exp^1|]])
      ++ concat [eq (q!idx) (q'!?[mix|exp^a,c|])
                | idx <- mixes q,
                  let a = facForVar idx x1,
                  a == facForVar idx x2,
                  let c = constFactor idx,
                  c /= 0]
      ++ concat [zero (q![mix|x1^a,c|])
                | idx <- mixes q,
                  onlyVarsOrConst idx [x1],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx x1]
      ++ concat [zero (q![mix|x2^a,c|])
                | idx <- mixes q,
                  onlyVarsOrConst idx [x2],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx x2]            
      ++ concat [zero (q'![mix|exp^a,c|]) 
                | idx <- mixes q',
                  let a = facForVar idx exp,
                  let c = constFactor idx,
                  [mix|x1^a,x2^a,c|] `S.notMember` (q^.ftCoeffs)]
cConst _ (Ast.Const id _) (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: Args -> FreeTemplate -> FreeTemplate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch _ q p x [] = extend p $
  [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
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
cMatch (Args {logL=cL, logR=cR, logLR=cLR}) q r x [u, v] = extend r $
  [(`eq` (q!x)) <$> def u,
   (`eq` (q!x)) <$> def v,
   (`eq` prod [ConstTerm cL, q!x]) <$> def [mix|u^1|],
   (`eq` prod [ConstTerm cR, q!x]) <$> def [mix|v^1|],
   (`eq` sum [
       q![mix|x^1|],
       prod [ConstTerm cLR, q!x]]) <$> def [mix|u^1,v^1|]]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,u^a,v^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x],
       not (null xs && b == 0)]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
-- tuple with one tree
cMatch _ q r x [v] = extend r $
  ((`eq` (q!x)) <$> def v)
  : [(`eq` (q!idx)) <$> def [mix|_xs,v^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
cMatch _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti _ ps' x is r_ = extend r_ $
  [(`eq` (ps'!!i![mix|exp^d,e|])) <$> def i
  | i <- is,
    let d = facForVar i x,
    let e = max 0 $ constFactor i]

cLetCf :: FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf q ps ps' x (gamma, delta) bdes = (psDefined, ps'Defined, psCs ++ ps'Cs ++ cs)
  where (psDefined, psCs) = extends ps $
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
            
        (ps'Defined, ps'Cs) = extends ps' $
          [(`le` sum [p!ac
                     | let p = psDefined!!bde,
                       ac <- S.toList $ idxs p]) <$> defEntry bde de
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
