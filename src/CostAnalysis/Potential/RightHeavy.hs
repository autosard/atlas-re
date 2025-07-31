module CostAnalysis.Potential.RightHeavy (pot, defaultPot) where

import CostAnalysis.Potential.RightHeavy.Base
import CostAnalysis.Potential.RightHeavy.Constraints
import CostAnalysis.Potential.RightHeavy.Optimization
import CostAnalysis.Potential.RightHeavy.Weakening
import CostAnalysis.Potential.Logarithm.Constraints
import CostAnalysis.Potential(Potential(Potential))


pot :: Args -> Potential
pot args = Potential
  template
  (ranges args)
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

defaultARange = [0,1]
defaultBRange = [0,1,2]

defaultPot = pot $ Args defaultARange defaultBRange
