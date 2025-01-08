module CostAnalysis.Potential.Log(pot, defaultPot, Args(..)) where

import CostAnalysis.Potential.Log.Base
import CostAnalysis.Potential.Log.Constraints
import CostAnalysis.Potential.Log.Optimization
import CostAnalysis.Potential.Log.Weakening
import CostAnalysis.Potential(Potential(Potential))
import Ast (PotentialKind(Logarithmic))

pot :: Args -> Potential
pot args = Potential
  Logarithmic
  rsrcAnn
  (ranges args)
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
  (cOptimize args)
  printBasePot

defaultPot = let _aRange = [0,1]
                 _bRange = [0,1,2]
                 args = Args _aRange _bRange in
               pot args
