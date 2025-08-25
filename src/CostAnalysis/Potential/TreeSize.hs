module CostAnalysis.Potential.TreeSize (pot, defaultPot) where

import CostAnalysis.Potential.TreeSize.Base
import CostAnalysis.Potential.TreeSize.Constraints
import CostAnalysis.Potential.TreeSize.Optimization
import CostAnalysis.Potential.TreeSize.Weakening
import CostAnalysis.Potential(Potential(Potential))
import CostAnalysis.Potential.Common(auxSigs)


pot :: Potential
pot = Potential
  template
  oneCoeff
  zeroCoeff
  monoFnCoeff
  cConst
  cMatch
  constCases
  cLetBodyMulti
  letCfIdxs
  cLetCf
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot
  auxSigs

defaultPot = pot 
