{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Potential.Log.Helper where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Text(Text)
import qualified Data.Text as T
import Data.List(intercalate)

import Primitive(Id)
import CostAnalysis.Coeff
import CostAnalysis.Potential(emptyAnn)
import CostAnalysis.Potential.Log
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

_aRange = [0,1] :: [Int]
_bRange = [0,1,2] :: [Int]

potArgs = Args _aRange _bRange 
pot = logPot potArgs

defaultRanges = (_aRange, _bRange)

empty :: [Factor]
empty = []

annArrayFromIdxs :: [CoeffIdx] -> Text -> [(Id,Type)] -> AnnArray
annArrayFromIdxs idxs label args = M.fromList $ map annFromIdx idxs
  where annFromIdx idx = (idx, emptyAnn pot 0 (label' idx) "" args)
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' idx = T.concat [label, "_", T.pack $ show idx]
