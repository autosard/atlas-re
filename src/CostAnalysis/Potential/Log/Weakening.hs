module CostAnalysis.Potential.Log.Weakening(cWeaken) where

import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.Rules

-- TODO
cWeaken :: Args ->
  [RuleArg] -> RsrcAnn -> RsrcAnn
  -> RsrcAnn -> RsrcAnn -> [Constraint]
cWeaken args ruleArgs q q' p p' = []
