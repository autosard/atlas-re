module CostAnalysis.Potential.NLog(pot, defaultPot, Args(..)) where

import CostAnalysis.Potential.NLog.Base
import CostAnalysis.Potential.NLog.Constraints
import CostAnalysis.Potential.NLog.Optimization
import CostAnalysis.Potential.NLog.Weakening
import CostAnalysis.Potential(Potential(Potential))
import Ast (PotentialKind(LinLog))

pot :: Args -> Potential
pot args = Potential
  LinLog
  bearesPotential
  ranges
  rsrcAnn
  constCoeff
  (forAllCombinations args)
  cConst 
  cMatch
  cLetBindingBase
  cLetBodyBase
  cLetBinding
  cLetBody
  (cLetCf args)
  cWeakenVar
  genExpertKnowledge
  cOptimize
  cExternal
  printBasePot

defaultPot = pot (Args {})
