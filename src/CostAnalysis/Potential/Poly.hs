module CostAnalysis.Potential.Poly(pot, defaultPot, Args(..)) where

import CostAnalysis.Potential.Poly.Base
import CostAnalysis.Potential.Poly.Constraints
import CostAnalysis.Potential.Poly.Optimization
import CostAnalysis.Potential.Poly.Weakening
import CostAnalysis.Potential(Potential(Potential))

pot :: Args -> Potential
pot args = Potential
  template
  (ranges args)
  oneCoeff
  zeroCoeff
  monoFnCoeff
  (cConst args)
  (cMatch args)
  constCases
  cLetBodyMulti
  letCfIdxs
  (cLetCf args)
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot

defaultPot = pot (Args 2)
