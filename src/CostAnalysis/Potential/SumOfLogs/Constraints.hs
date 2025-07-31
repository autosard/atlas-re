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
import CostAnalysis.Potential.SumOfLogs.Base(Args(..), TreeInvariant(..))
import Data.List.Extra (groupSort)
import Ast
import qualified Data.Text as T
import CostAnalysis.Predicate (Predicate(..), predApplySubst)
import Data.Set (Set)


exp :: Id
exp = "e1"

constCases :: Args -> Pattern Positioned -> [Predicate]
constCases _ (ConstPat _ "leaf" _) = []
constCases args p@(ConstPat _ "node" [Id _ t, _, Id _ u])
  = case invariant args of
      Just (TreeInvariant m op flip) -> if flip
        then [Predicate m op u t [] (getType p)]
        else [Predicate m op t u [] (getType p)]
      Nothing -> []

cConst :: Args -> PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst _ (Leaf {}) _ (q, _) q'
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
cConst (Args {logL=cL, logR=cR, logLR=cLR}) e@(Node (Var x1) _ (Var x2)) _ (q, qe) q'
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
      ++ concat [geZero (q![mix|x1^a,c|])
                | idx <- mixes q,
                  onlyVarsOrConst idx [x1],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx x1]
      ++ concat [geZero (q![mix|x2^a,c|])
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
cConst _ (Ast.Const id _) _ (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: Args -> FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch _ q p _ x [] = extend p $
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
cMatch (Args {logL=cL, logR=cR, logLR=cLR}) q r _ x [u, v] = extend r $
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
cMatch _ q r _ x [v] = extend r $
  ((`eq` (q!x)) <$> def v)
  : [(`eq` (q!idx)) <$> def [mix|_xs,v^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
cMatch _ _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys
