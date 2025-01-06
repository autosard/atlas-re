module CostAnalysis.Potential.Poly(pot, defaultPot, Args(..)) where

import CostAnalysis.Potential.Poly.Base
import CostAnalysis.Potential.Poly.Constraints
import CostAnalysis.Potential.Poly.Optimization
import CostAnalysis.Potential.Poly.Weakening
import CostAnalysis.Potential(Potential(Potential))
import Ast (PotentialKind(Polynomial))

pot :: Args -> Potential
pot args = Potential
  Polynomial
  rsrcAnn
  (ranges args)
  oneCoeff
  zeroCoeff
  (cConst args)
  (cMatch args)
  cLetBodyMulti
  letCfIdxs
  (cLetCf args)
  genExpertKnowledge
  cExternal
  cOptimize
  printBasePot

defaultPot = pot (Args 2)
