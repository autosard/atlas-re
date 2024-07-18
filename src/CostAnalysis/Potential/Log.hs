module CostAnalysis.Potential.Log(logPot, Args(..)) where

import CostAnalysis.Potential.Log.Base
import CostAnalysis.Potential.Log.Constraints
import CostAnalysis.Potential.Log.Optimization
import CostAnalysis.Potential.Log.Weakening
import CostAnalysis.Potential(Potential(Potential))

logPot :: Args -> Potential
logPot args = Potential
  types
  (rsrcAnn args)
  constCoeff
  (forAllCombinations args)
  (cPlusConst args)
  (cMinusVar args)
  (cPlusMulti args)
  (cEq args)
  (cMatch args)
  (cLetBase args)
  (cLet args)
  (cWeakenVar args)
  (genExpertKnowledge args)
  (cOptimize args)
  printBasePot
