module CostAnalysis.Potential.Log(pot, Args(..)) where

import CostAnalysis.Potential.Log.Base
import CostAnalysis.Potential.Log.Constraints
import CostAnalysis.Potential.Log.Optimization
import CostAnalysis.Potential.Log.Weakening
import CostAnalysis.Potential(Potential(Potential))

pot :: Args -> Potential
pot args = Potential
  bearesPotential
  (ranges args)
  rsrcAnn
  constCoeff
  forAllCombinations
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
