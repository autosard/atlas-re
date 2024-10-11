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
  bearesPotential
  (ranges args)
  rsrcAnn
  constCoeff
  (forAllCombinations args)
  (cConst args)
  (cMatch args)
  cLetBindingBase
  cLetBodyBase
  cLetBinding
  cLetBody
  (cLetCf args)
  cWeakenVar
  genExpertKnowledge
  cOptimize
  cExternal
  printBasePot

defaultPot = pot (Args 2)
