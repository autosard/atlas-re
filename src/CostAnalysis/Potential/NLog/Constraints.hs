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

shiftLogs :: Int -> Int -> Maybe (Int, Int)
shiftLogs b c | c < 2 || b == 0 = Just (b, c + b)
              | otherwise = Nothing
              
-- addShiftL :: RsrcAnn -> RsrcAnn -> [Constraint] 
-- addShiftL q q' =
--   let [x] = _args q
--       [y] = _args q' in
--     concat $ [eqs
--              | idx <- mixes q,
--                let (a,b) = facForVar2 idx x,
--                let c = constFactor idx,
--                let a' = a - 1,
--                let eqs = case shiftLogs b c of
--                     Just (b', c') ->
--                       if a > 0 then
--                         eq (q!idx) (q'![mix|y^(a,b'),c'|])
--                         ++ eq (q!idx) (q'![mix|y^(a',b'),c'|])
--                       else
--                         eq (q!idx) (q'![mix|y^(a,b'),c'|])
--                     Nothing -> eq (q!idx) (ConstTerm 0)]
  
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

cLetBodyMulti :: AnnArray -> Id -> [CoeffIdx] -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyMulti _ _ _ r_ = (r_, [])

cLetCf :: Args -> RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (AnnArray, AnnArray, [Constraint])
cLetCf potArgs q ps ps' x (gamma, delta) js = error "undefined for univariate potential."
