{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.RightHeavy.Constraints where

import Prelude hiding (exp, (!!), sum, or)
import qualified Data.List as L
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le, Lt)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.RightHeavy.Base(oneCoeff)
import Ast hiding (PotentialKind(..))
import CostAnalysis.Annotation(Measure(..))
import Data.List.Extra (groupSort)
import qualified Data.Text as T
import Data.Set (Set)
import CostAnalysis.Predicate (Predicate (Predicate), PredOp (..), anyImplies)


exp :: Id
exp = "e1"

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst (Leaf {}) _ (q, qe) q'
  = concat [eqSum (q![mix|c|]) ([q'!?[mix|exp^a,b|]
                                | a <- [0..c],
                                  let b = c - a,
                                  a + b == c])
           | idx <- mixes q,
             let c = constFactor idx,
             c >= 2]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=1) . map constFactor) (mixes q),
         idx <- mixes q',
         idxSum idx >= 2,
         idxSum idx `S.notMember` qConsts]
cConst e@(Node (Var t) _ (Var u)) preds (q, qe) q'
  = case anyImplies preds (Predicate Weight Le u t [] (getType e)) of
      (True, preCondition) ->
        caseIndependentCs
        ++ zero (q!?oneCoeff) 
        ++ preCondition
      (False, _) -> 
        caseIndependentCs 
        ++ eq (q!?oneCoeff) (q'!?exp)
  where caseIndependentCs =
          eq (q!?t) (q'!?exp)
          ++ eq (q!?u) (q'!?exp)
          ++ concat [eq (q!idx) (q'!?[mix|exp^a,c|])
                | idx <- mixes q,
                  let a = facForVar idx t,
                  a == facForVar idx u,
                  let c = constFactor idx]
          ++ concat [geZero (q![mix|t^a,c|])
                | idx <- mixes q,
                  onlyVarsOrConst idx [t],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx t]
          ++ concat [geZero (q![mix|u^a,c|])
                | idx <- mixes q,
                  onlyVarsOrConst idx [u],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx u]            
          ++ concat [zero (q'![mix|exp^a,c|]) 
                | idx <- mixes q',
                  let a = facForVar idx exp,
                  let c = constFactor idx,
                  [mix|t^a,u^a,c|] `S.notMember` idxs q]
  
cConst (Ast.Const id _) preds (q, _) q' = error $ "Constructor '" ++ T.unpack id ++ "' not supported."
      
cMatch :: FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- leaf  
cMatch q p _ x [] = extend p $
  [(`eq` (q!y)) <$> def y | y <- L.delete x (args q)]
  ++ [(`eqSum` qs) <$> def [mix|_xs, c|]
     | ((xs, c), qs) <- sums]
  where sums = groupSort $
            [((xs, c), q!idx) 
            | idx <- mixes q,
              let a = facForVar idx x,
              let b = constFactor idx,
              a >= 0, b >= 0,
              let c = a + b,
              let xs = varsExcept idx [x]]
-- node
cMatch q r (Just (Predicate Weight Lt x_ y_ _ _)) x [t, u]
  | x_ == t, y_ == u
  = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u,
    (`eqSum` [q!x,q!oneCoeff]) <$> def oneCoeff
  ]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,t^a,u^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x],
       not (a == 0 && b == 2)]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
cMatch q r (Just (Predicate Weight Le x_ y_ _ _)) x [t, u]
  | x_ == u, y_ == t
  = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u
  ]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,t^a,u^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]  
cMatch _ _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

constCases :: Pattern Positioned -> [Predicate]
constCases (ConstPat _ "leaf" _) = []
constCases p@(ConstPat _ "node" [Id _ t, _, Id _ u])
  = [Predicate Weight Lt t u [] (getType p),
     Predicate Weight Le u t [] (getType p)]

