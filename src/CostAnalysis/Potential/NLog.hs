module CostAnalysis.Potential.NLog(pot, defaultPot, Args(..)) where

import CostAnalysis.Potential.NLog.Base
import CostAnalysis.Potential.NLog.Constraints
import CostAnalysis.Potential.NLog.Optimization
import CostAnalysis.Potential.NLog.Weakening
import CostAnalysis.Potential(Potential(Potential))
import CostAnalysis.Potential.Common(auxSigs)

pot :: Args -> Potential
pot args = Potential
  template
  ranges
  oneCoeff
  zeroCoeff
  monoFnCoeff
  cConst
  cMatch
  constCases
  cLetBodyMulti
  (letCfIdxs args)
  (cLetCf args)
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot
  auxSigs

defaultPot = pot (Args {})
