{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.NLog.Constraints where

import Prelude hiding (exp, (!!), sum)

import Primitive(Id)
import CostAnalysis.Potential.NLog.Base
import CostAnalysis.Template
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Coeff
import Ast 
import qualified Data.Text as T
import Data.List.Extra (groupSort)

exp :: Id
exp = "e1"

shiftLogs :: Int -> Int -> Maybe (Int, Int)
shiftLogs b c | c < 2 || b == 0 = Just (b, c + b)
              | otherwise = Nothing
  
addShiftDefL :: FreeTemplate -> Id -> FreeTemplate -> Id -> (FreeTemplate, [Constraint])
addShiftDefL q_ x q' y = extend q_ $
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

cConst :: PositionedExpr -> (FreeTemplate, FreeTemplate) -> FreeTemplate -> [Constraint]
cConst (Nil {}) (q, _) q' = eqSum (q!oneCoeff) [
  q'![mix|exp^(1,0),2|],
  q'![mix|exp^(0,1),1|],
  q'![mix|exp^(1,1),1|],
  q'!oneCoeff]
  ++ eq (q![mix|1|]) (q'![mix|exp^(0,1)|])
cConst (Ast.Const id _) _ _ = error $ "Constructor '" ++ T.unpack id ++ "' not supported."

cMatch :: FreeTemplate -> FreeTemplate -> Id -> [Id] -> (FreeTemplate, [Constraint])
-- nil / leaf
cMatch q r x [] = extend r $
  ((`eqSum` [q![mix|x^(1,0),2|],
            q![mix|x^(0,1),1|],
            q![mix|x^(1,1),1|],
            q!oneCoeff]) <$> def oneCoeff)
  : [(`eq` (q![mix|x^(0,1)|])) <$> def [mix|1|]]
-- cons                   
cMatch q p x [l] = addShiftDefL p l q x

cLetBodyMulti :: FreeTemplate -> TemplateArray -> Id -> [CoeffIdx] -> FreeTemplate -> (FreeTemplate, [Constraint])
cLetBodyMulti q _ _ _ r = extend r $
  [ (`eq` (q!idx)) <$> def idx
  | idx <- mixes q,
    onlyVarsOrConst idx (args r)]

cLetCf :: Args -> FreeTemplate -> TemplateArray -> TemplateArray -> Id -> ([Id], [Id]) -> [CoeffIdx] -> (TemplateArray, TemplateArray, [Constraint])
cLetCf potArgs q ps ps' x (gamma, delta) js = error "undefined for univariate potential."
