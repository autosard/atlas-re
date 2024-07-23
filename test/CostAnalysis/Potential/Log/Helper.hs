{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.Log.Helper where

import qualified Data.Set as S
import Data.Text(Text)

import Primitive(Id)
import CostAnalysis.Coeff
import CostAnalysis.Potential.Log.Base hiding (rsrcAnn)
import qualified CostAnalysis.Potential.Log.Base as B(rsrcAnn)
import Typing.Type (Type)
import CostAnalysis.RsrcAnn

arrIdx :: [Factor] -> S.Set Factor
arrIdx = S.fromList

coeff :: [Factor] -> (CoeffIdx, Coeff)
coeff idx = let idx' = Mixed . S.fromList $ idx in
  (idx', Coeff 0 "Q" "log" idx')

coeff' :: Id -> (CoeffIdx, Coeff)
coeff' id = let idx = Pure id in
  (idx, Coeff 0 "Q" "log" idx)

_aRange = [0,1]
_bRange = [0,2]

potArgs :: Args
potArgs = Args _aRange _bRange _aRange _bRange (-1 : _bRange)

empty :: [Factor]
empty = []

rsrcAnn :: Int -> Text -> [(Id, Type)] -> RsrcAnn
rsrcAnn id label vars = fst $ B.rsrcAnn potArgs id label vars
