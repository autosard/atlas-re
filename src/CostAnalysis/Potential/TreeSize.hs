module CostAnalysis.Potential.TreeSize (pot, defaultPot) where

import CostAnalysis.Potential.TreeSize.Base
import CostAnalysis.Potential.TreeSize.Constraints
import CostAnalysis.Potential.TreeSize.Optimization
import CostAnalysis.Potential.TreeSize.Weakening
import CostAnalysis.Potential(Potential(Potential))


pot :: Potential
pot = Potential
  template
  ranges
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

defaultPot = pot 
