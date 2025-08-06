{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.RightHeavy.Constraints where

import Prelude hiding (exp, (!!), sum, or, (^))
import qualified Data.List as L
import qualified Data.Set as S

import Primitive(Id, traceShow)
import CostAnalysis.Template hiding (sum, sub)
import CostAnalysis.Constraint hiding (Le, Lt)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import CostAnalysis.Potential.RightHeavy.Base(oneCoeff)
import qualified CostAnalysis.Potential.Logarithm.Constraints as Log
import Ast hiding (PotentialKind(..))
import CostAnalysis.Annotation(Measure(..))
import Data.List.Extra (groupSort)
import qualified Data.Text as T
import Data.Set (Set)
import CostAnalysis.Predicate (Predicate (Predicate), PredOp (..), anyImplies)
import CostAnalysis.Coeff (facForVar2)


exp :: Id
exp = "e1"

cConst :: PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst (Leaf {}) _ (q, qe) q'
  = concat [eqSum (q![mix|c|]) ([q'!?[mix|exp^a,b|]
                                | a <- [0..c],
                                  let b = c - a,
                                  a + b == c])
           | idx <- mixes1 q,
             let c = constFactor idx,
             c >= 2]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=1) . map constFactor) (mixes1 q),
         idx <- mixes1 q',
         idxSum idx >= 2,
         idxSum idx `S.notMember` qConsts]
cConst e@(Node (Var t) _ (Var u)) preds (q, qe) q'
  = caseIndependentCs 
    ++ eq (q!?[mix|t^(1,1),u^(2,1)|]) (q'!?exp)
  where caseIndependentCs =
          eq (q!?t) (q'!?exp)
          ++ eq (q!?u) (q'!?exp)
          ++ concat [eq (q!idx) (q'!?[mix|exp^a,c|])
                | idx <- mixes1 q,
                  let a = facForVar idx t,
                  a == facForVar idx u,
                  let c = constFactor idx]
          ++ concat [geZero (q![mix|t^a,c|])
                | idx <- mixes1 q,
                  onlyVarsOrConst idx [t],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx t]
          ++ concat [geZero (q![mix|u^a,c|])
                | idx <- mixes1 q,
                  onlyVarsOrConst idx [u],
                  let c = constFactor idx,
                  c /= 0,
                  let a = facForVar idx u]            
          ++ concat [zero (q'![mix|exp^a,c|]) 
                | idx <- mixes1 q',
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
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes2 q,
       x `notElem` coeffArgs idx]   
  where sums = groupSort $
            [((xs, c), q!idx) 
            | idx <- mixes1 q,
              let a = facForVar idx x,
              let b = constFactor idx,
              a >= 0, b >= 0,
              let c = a + b,
              let xs = varsExcept idx [x]]

-- node
cMatch q r _ x [t, u]
  = extend r $
  [
    (`eq` (q!x)) <$> def t,
    (`eq` (q!x)) <$> def u,
    (`eq` (q!x)) <$> def [mix|t^(1,1),u^(2,1)|]
  ]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,t^a,u^a,b|]
     | idx <- mixes1 q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!?z)) <$> def z | (Pure z) <- pures q, z /= x]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,t^(a,b),u^(a,b)|]
     | idx <- mixes2 q,
       let (a,b) = facForVar2 idx x,
       let xs = varsExcept idx [x]]

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti q ps' x is r_ = extend r_ $
  [(`eq` (ps'!!i![mix|exp^d,e|])) <$> def i
  | i <- restrictFacs1 is,
    let d = facForVar i x,
    let e = max 0 $ constFactor i]
  ++ [(`eq` (ps'!!i!exp)) <$> def i
     | i <- restrictFacs2 is]
  ++ [(`eq` (q!i)) <$> def i
     | i <- mixes2 q,
       onlyVars i (args r_)]


cLetCf q _ps _ps' x (gamma, delta) bdes
  = let (ps, ps', _cs) = Log.cLetCf q _ps _ps' x (gamma, delta) bdes 
        (psDefined, psCs) = extends ps $
                            [(`eq` sum [q!idx
                                       | idx <- mixes2 q,
                                         ys == varsForFac idx [2,1],
                                         let xs = varsForFac idx [1,1],
                                         z `elem` xs])
                             <$> defEntry [mix|_bs,x^(1,1)|] (Pure z)
                            | idx <- mixes2 q,
                              let xs = varsForFac idx [1,1] ,
                              all (`elem` gamma) xs,
                              let ys = varsForFac idx [2,1],
                              let bs = varsRestrict idx ys,
                              all (`elem` delta) ys,
                              z <- xs] 
        (ps'Defined, ps'Cs) = extends ps' $
                              [(`le` ConstTerm 1) <$> defEntry bde (Pure exp)
                              | bde <- restrictFacs2 bdes]
        cs = concat [ geZero (q!idx)
                    | idx <- mixes2 q,
                      let xs = varsForFac idx [1,1],
                      all (`elem` delta) xs,
                      let ys = varsForFac idx [2,1],
                      all (`elem` gamma) ys] in
  (psDefined, ps'Defined, _cs ++ psCs ++ ps'Cs ++ cs)
        

constCases :: Pattern Positioned -> [Predicate]
constCases _ = []
