module CostAnalysis.Potential.RightHeavy (pot, defaultPot) where

import CostAnalysis.Potential.RightHeavy.Base
import CostAnalysis.Potential.RightHeavy.Constraints
import CostAnalysis.Potential.RightHeavy.Optimization
import CostAnalysis.Potential.RightHeavy.Weakening
import qualified CostAnalysis.Potential.Logarithm.Constraints as Log
import CostAnalysis.Potential(Potential(Potential))


pot :: Args -> Potential
pot args = Potential
  (template args)
  oneCoeff
  zeroCoeff
  monoFnCoeff
  cConst
  cMatch
  constCases
  cLetBodyMulti
  (letCfIdxs args)
  cLetCf
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot
  auxSigs

defaultARange = [0,1]
defaultBRange = [-1,0,1,2]

defaultPot = pot $ Args defaultARange defaultBRange
