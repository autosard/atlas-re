{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module CostAnalysis.Log where

import qualified Data.Map as M
import Data.List(intercalate)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set(Set)
import Prelude hiding ((!!), (^), exp)
import qualified Prelude as P((^))
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Rules ( RuleArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential(Potential (Potential))       
import CostAnalysis.Optimization
import Typing.Type


