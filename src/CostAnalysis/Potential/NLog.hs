module CostAnalysis.Potential.NLog(pot, defaultPot, Args(..)) where

import CostAnalysis.Potential.NLog.Base
import CostAnalysis.Potential.NLog.Constraints
import CostAnalysis.Potential.NLog.Optimization
import CostAnalysis.Potential.NLog.Weakening
import CostAnalysis.Potential(Potential(Potential))
import Ast (PotentialKind(LinLog))

pot :: Args -> Potential
pot args = Potential
  rsrcAnn
  ranges
  oneCoeff
  zeroCoeff
  monoFnCoeff
  cConst 
  cMatch
  cLetBodyMulti
  (letCfIdxs args)
  (cLetCf args)
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot

defaultPot = pot (Args {})
