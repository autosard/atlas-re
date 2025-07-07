module CostAnalysis.Potential.Rank (pot, defaultPot) where

import CostAnalysis.Potential.Rank.Base
import CostAnalysis.Potential.Rank.Constraints
import CostAnalysis.Potential.Rank.Optimization
import CostAnalysis.Potential.Rank.Weakening
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
  cLetBodyMulti
  letCfIdxs
  cLetCf
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot

defaultPot = pot 
