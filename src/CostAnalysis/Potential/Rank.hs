module CostAnalysis.Potential.Rank (pot, defaultPot) where

import CostAnalysis.Potential.Rank.Base
import CostAnalysis.Potential.Rank.Constraints
import CostAnalysis.Potential.Rank.Optimization
import CostAnalysis.Potential.Rank.Weakening
import CostAnalysis.Potential(Potential(Potential))
import CostAnalysis.Potential.Common(auxSigs)


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
