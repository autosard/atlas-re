module CostAnalysis.Potential.Log(logPot, Args(..)) where

import CostAnalysis.Potential.Log.Base
import CostAnalysis.Potential.Log.Constraints
import CostAnalysis.Potential.Log.Optimization
import CostAnalysis.Potential.Log.Weakening
import CostAnalysis.Potential(Potential(Potential))

logPot :: Args -> Potential
logPot args = Potential
  bearesPotential
  (ranges args)
  rsrcAnn
  constCoeff
  cConst
  cMatch 
  cLetBindingBase
  cLetBodyBase
  cLetBinding
  cLetBody
  cLetCf
  cWeakenVar
  genExpertKnowledge
  (cOptimize args)
  printBasePot
