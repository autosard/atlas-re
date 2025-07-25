{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Poly.Constraints where

import Prelude hiding (exp, (!!), sum)
import qualified Data.List as L

import Primitive(Id)
import CostAnalysis.Potential.Poly.Base
import CostAnalysis.Template
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import Ast 
import CostAnalysis.Predicate (Predicate)
import Data.Set (Set)

exp :: Id
exp = "e1"

constCases :: Pattern Positioned -> [Predicate]
constCases _ = []

-- additative shift
addShiftL :: Int -> FreeTemplate -> FreeTemplate -> [Constraint] 
addShiftL k q q' = let [x] = args q
                       [y] = args q' in
  concat [if idxSum idx < k then
             eqSum (q!idx) [q'!?[mix|_is,y^j|], q'!?[mix|_is,y^j'|]]
          else
             eq (q!idx) (q'!?[mix|_is,y^j|])
         | idx <- mixes q,
           let j = facForVar idx x,
           let j' = j+1,
           let is = varsExcept idx [x]]

addShiftDefL :: Int -> FreeTemplate -> Id -> FreeTemplate -> Id -> (FreeTemplate, [Constraint])
addShiftDefL k q_ x q' y = extend q_ $
  [if idxSum idx < k then
     (`eqSum` [q'![mix|_is,y^j|], q'![mix|_is,y^j'|]]) <$> def [mix|_is,x^j|]
   else
     (`eq` (q'![mix|_is,y^j|])) <$> def [mix|_is,x^j|]
  | idx <- mixes q',
    let j = facForVar idx y,
    let j' = j+1,
    let is = varsExcept idx [y]]

cConst :: Args -> PositionedExpr -> Set Predicate -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst potArgs (Nil {}) _ (q, _) q'
  = eq (q![mix||]) (q'!?[mix||])
  -- cons
cConst potArgs (Cons {}) _ (q, _) q' = addShiftL (degree potArgs) q q' 
cConst _ (Tuple (Var x1) (Var x2)) _ (q, _) q' = unifyAssertEqBy q q' [x1,x2]
cConst _ constr _ _ _ = error $ show constr

cMatch :: Args -> FreeTemplate -> FreeTemplate -> Maybe Predicate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- nil 
cMatch _ q r _ x [] = extend r $
  [(`eq` (q!idx)) <$> def idx
  | idx <- mixes q,
    onlyVars idx (args r)]
-- cons                   
cMatch potArgs q p _ x [l] = addShiftDefL (degree potArgs) p l q x

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti _ ps' x is r_ = extend r_ $
  [(`eq` (ps'!!i!pIdx)) <$> def [mix|_b,x^d|]
  | i <- is,
    let b = idxToSet i,
    pIdx <- mixes $ ps'!!i,
    let d = facForVar pIdx exp]

cLetCf :: Args -> FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf potArgs q ps ps' x (gamma, delta) js = (psDefined, ps'Defined, psCs)
  where (psDefined, psCs) = extends ps $
          [(`eq` (q!idx)) <$> defEntry j [mix|_i|]
          | j <- js,
            idx <- mixes q,
            idxToSet j == varsRestrict idx delta,
            let i = varsRestrict idx gamma,
            (not . null) (varsRestrict idx delta)]
        -- assume shape for p'_j  
        (ps'Defined, _) = extends ps' $ [L.singleton <$> defEntry j [mix|exp^d|]
                                           | j <- js,
                                             let j' = idxToSet j,
                                             d <- [0..degree potArgs],
                                             idxSum [mix|_j',exp^d|] <= degree potArgs]

