{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Poly.Constraints where

import Prelude hiding (exp, (!!), sum)
import qualified Data.List as L

import Primitive(Id)
import CostAnalysis.Potential.Poly.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import Ast 

exp :: Id
exp = "e1"

-- additative shift
addShiftL :: Int -> RsrcAnn -> RsrcAnn -> [Constraint] 
addShiftL k q q' = let [x] = _args q
                       [y] = _args q' in
  concat [if idxSum idx < k then
             eqSum (q!idx) [q'!?[mix|_is,y^j|], q'!?[mix|_is,y^j'|]]
          else
             eq (q!idx) (q'!?[mix|_is,y^j|])
         | idx <- mixes q,
           let j = facForVar idx x,
           let j' = j+1,
           let is = varsExcept idx [x]]

addShiftDefL :: Int -> RsrcAnn -> Id -> RsrcAnn -> Id -> (RsrcAnn, [Constraint])
addShiftDefL k q_ x q' y = extendAnn q_ $
  [if idxSum idx < k then
     (`eqSum` [q'![mix|_is,y^j|], q'![mix|_is,y^j'|]]) <$> def [mix|_is,x^j|]
   else
     (`eq` (q'![mix|_is,y^j|])) <$> def [mix|_is,x^j|]
  | idx <- mixes q',
    let j = facForVar idx y,
    let j' = j+1,
    let is = varsExcept idx [y]]

cConst :: Args -> PositionedExpr -> RsrcAnn -> RsrcAnn -> [Constraint]
cConst potArgs (Nil {}) q q'
  = eq (q![mix||]) (q'!?[mix||])
  -- cons
cConst potArgs (Cons {}) q q' = addShiftL (degree potArgs) q q' 
cConst _ (Tuple (Var x1) (Var x2)) q q' = annLikeUnify' q q' [x1,x2]
cConst _ constr _ _ = error $ show constr

cMatch :: Args -> RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint])
-- nil / leaf
cMatch _ q r x [] = extendAnn r $
  [(`eq` (q!idx)) <$> def idx
  | idx <- mixes q,
    onlyVars idx (argVars r)]
-- cons                   
cMatch potArgs q p x [l] = addShiftDefL (degree potArgs) p l q x

cLetBindingBase :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBindingBase q p = extendAnn p $
  [(`eq` (q!idx)) <$> def idx
  | idx <- mixes q,
    onlyVarsOrConst idx xs]
  where xs = annVars p

cLetBodyBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyBase q r p' = extendAnn r $
  [(`eq` (q!idx)) <$> def idx
  | idx <- mixes q,
    onlyVarsOrConst idx ys,
    idx /= oneCoeff]
  where ys = annVars r

cLetBinding :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBinding q p = extendAnn p $
  [(`eq` (q!idx)) <$> def idx
  | idx <- mixes q,
    onlyVarsOrConst idx xs,
    idx /= oneCoeff]
  -- move const
  ++ [(`le` (q!?oneCoeff)) <$> def oneCoeff]
  where xs = annVars p

cLetBody :: RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> AnnArray -> Id -> [CoeffIdx] -> (RsrcAnn, [Constraint])
cLetBody q r p p' ps' x js = extendAnn r $
  [(`eq` (p'!pIdx)) <$> def [mix|x^d|]
  | pIdx <- mixes p',
    let d = facForVar pIdx exp,
    d /= 0]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx ys,
       idx /= oneCoeff]
  ++ [(`eq` sum [sub [q!?oneCoeff, p!oneCoeff], p'!oneCoeff]) <$> def oneCoeff]
  ++ [(`eq` (ps'!!j!pIdx)) <$> def [mix|_j',x^d|]
     | j <- js,
       let j' = idxToSet j,
       pIdx <- mixes $ ps'!!j,
       let d = facForVar pIdx exp]
  where ys = L.delete x (annVars r)

cLetCf :: Args -> RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (AnnArray, AnnArray, [Constraint])
cLetCf potArgs q ps ps' x (gamma, delta) js = (psDefined, ps'Defined, psCs)
  where (psDefined, psCs) = extendAnns ps $
          [(`eq` (q!idx)) <$> defEntry j [mix|_i|]
          | j <- js,
            idx <- mixes q,
            idxToSet j == varsRestrict idx delta,
            let i = varsRestrict idx gamma,
            (not . null) (varsRestrict idx delta)]
        -- assume shape for p'_j  
        (ps'Defined, _) = extendAnns ps' $ [L.singleton <$> defEntry j [mix|exp^d|]
                                           | j <- js,
                                             let j' = idxToSet j,
                                             d <- [0..degree potArgs],
                                             idxSum [mix|_j',exp^d|] <= degree potArgs]

