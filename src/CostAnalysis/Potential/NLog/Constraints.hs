{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.NLog.Constraints where

import Prelude hiding (exp, (!!), sum)
import qualified Data.List as L

import Primitive(Id)
import CostAnalysis.Potential.NLog.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import Ast 
import CostAnalysis.Potential (AnnRanges(rangeA, rangeB))
import qualified Data.Text as T
import Data.List.Extra (groupSort)

exp :: Id
exp = "e1"

-- shiftLogs :: Int -> Int -> Maybe (Int, Int)
-- shiftLogs 1 0 = Just (0, 1)
-- shiftLogs 0 0 = Just (0, 0)
-- shiftLogs 0 1 = Nothing

shiftLogs :: Int -> Int -> Maybe (Int, Int)
shiftLogs b c | c < 2 || b == 0 = Just (b, c + b)
              | otherwise = Nothing
              
addShiftL :: RsrcAnn -> RsrcAnn -> [Constraint] 
addShiftL q q' =
  let [x] = _args q
      [y] = _args q' in
    concat $ [eqs
             | idx <- mixes q,
               let (a,b) = facForVar2 idx x,
               let c = constFactor idx,
               let a' = a - 1,
               let eqs = case shiftLogs b c of
                    Just (b', c') ->
                      if a > 0 then
                        eq (q!idx) (q'![mix|y^(a,b'),c'|])
                        ++ eq (q!idx) (q'![mix|y^(a',b'),c'|])
                      else
                        eq (q!idx) (q'![mix|y^(a,b'),c'|])
                    Nothing -> eq (q!idx) (ConstTerm 0)]
                            

addShiftDefL :: RsrcAnn -> Id -> RsrcAnn -> Id -> (RsrcAnn, [Constraint])
addShiftDefL q_ x q' y = extendAnn q_ $
  [ (`eqSum` map (q'!) q'Idxs) <$> def qIdx
  | (qIdx, q'Idxs) <- groupSort nonZeroIdxs]
  where split idx (left, right) =
           let (a, b) = facForVar2 idx y
               c = constFactor idx
               a' = a - 1 in
           case shiftLogs b c of
                Just (b', c') -> (left, right ++ if a > 0 then
                                     [([mix|x^(a, b'), c'|], idx),
                                      ([mix|x^(a',b'), c'|], idx)]
                                   else [([mix|x^(a, b'), c'|], idx)])
                Nothing -> (idx:left, right)
        (zeroIdxs, nonZeroIdxs) = foldr split ([],[]) (mixes q')

cConst :: PositionedExpr -> RsrcAnn -> RsrcAnn -> [Constraint]
cConst (Nil {}) q q' = eqSum (q!oneCoeff) [
  q'![mix|exp^(1,0),2|],
  q'![mix|exp^(0,1),1|],
  q'![mix|exp^(1,1),1|],
  q'!oneCoeff]
  ++ eq (q![mix|1|]) (q'![mix|exp^(0,1)|])
cConst (Ast.Const id _) _ _ = error $ "Constructor '" ++ T.unpack id ++ "' not supported."

cMatch :: RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint])
-- nil / leaf
cMatch q r x [] = extendAnn r $
  ((`eqSum` [q![mix|x^(1,0),2|],
            q![mix|x^(0,1),1|],
            q![mix|x^(1,1),1|],
            q!oneCoeff]) <$> def oneCoeff)
  : [(`eq` (q![mix|x^(0,1)|])) <$> def [mix|1|]]
-- cons                   
cMatch q p x [l] = addShiftDefL p l q x

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
  [(`eq` (p'!pIdx)) <$> def [mix|x^(a,b),c|]
  | pIdx <- mixes p',
    let (a, b) = facForVar2 pIdx exp,
    let c = constFactor pIdx,
    a /= 0 || b /= 0 || c /= 0]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx ys,
       idx /= oneCoeff]
  ++ [(`eq` sum [sub [q!?oneCoeff, p!oneCoeff], p'!oneCoeff]) <$> def oneCoeff]
  ++ [(`eq` (ps'!!j!pIdx)) <$> def [mix|_j',x^(a, b), c|]
     | j <- js,
       let j' = idxToSet j,
       pIdx <- mixes $ ps'!!j,
       let (a, b) = facForVar2 pIdx exp,
       let c = constFactor pIdx]
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
        (ps'Defined, _) = extendAnns ps' $
          [L.singleton <$> defEntry j idx
          | j <- js,
            idx <- defaultCoeffs ["e"] (rangeA ranges, rangeB ranges)]

cWeakenVar :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cWeakenVar q r = let xs = annVars r in
  extendAnn r $
    [(`eq` (q!idx)) <$> def idx
    | idx <- mixes q,
      onlyVarsOrConst idx xs]

