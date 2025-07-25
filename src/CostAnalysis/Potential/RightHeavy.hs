module CostAnalysis.Potential.RightHeavy (pot, defaultPot) where

import CostAnalysis.Potential.RightHeavy.Base
import CostAnalysis.Potential.RightHeavy.Constraints
import CostAnalysis.Potential.RightHeavy.Optimization
import CostAnalysis.Potential.RightHeavy.Weakening
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
