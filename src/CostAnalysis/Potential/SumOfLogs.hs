module CostAnalysis.Potential.SumOfLogs (pot, defaultPot, logrPot, loglrxPot, goldenPot, Args (..)) where

import CostAnalysis.Potential.SumOfLogs.Base
import CostAnalysis.Potential.SumOfLogs.Constraints
import CostAnalysis.Potential.SumOfLogs.Optimization
import CostAnalysis.Potential.SumOfLogs.Weakening
import CostAnalysis.Potential(Potential(Potential))

import Data.Ratio((%))

pot :: Args -> Potential
pot args = Potential
  template
  (ranges args)
  oneCoeff
  zeroCoeff
  monoFnCoeff
  (cConst args)
  (cMatch args)
  cLetBodyMulti
  letCfIdxs
  cLetCf
  (genExpertKnowledge args)
  cExternal
  (cOptimize args)
  printBasePot


defaultARange = [0,1]
defaultBRange = [0,1,2]

defaultPot = pot $ Args {
  aRange=defaultARange,
  bRange=defaultBRange,
  logL=1,
  logR=1,
  logLR=0,
  logLemmaInstance=LogLemmaCoeffs 1 1 2 2} 

logrPot = pot $ Args {
  aRange=defaultARange,
  bRange=defaultBRange,
  logL=0,
  logR=1%2,
  logLR=0,
  logLemmaInstance=LogLemmaCoeffs (1%2) (1%2) 1 1}

loglrxPot = pot $ Args {
  aRange=defaultARange,
  bRange=defaultBRange,
  logL=(-1)%2,
  logR=0,
  logLR=1%2,
  logLemmaInstance=LogLemmaCoeffs (1%2) (1%2) 1 1}   

goldenPot = pot $ Args {
  aRange=defaultARange,
  bRange=defaultBRange,
  logL=(-a),
  logR=0,
  logLR=a,
  logLemmaInstance=LogLemmaCoeffs b a (a+b) 1}
  where -- a = \phi b where \phi is the (approximated) golden ratio
        a = 105 % 163
        b = 3115 % 7824
