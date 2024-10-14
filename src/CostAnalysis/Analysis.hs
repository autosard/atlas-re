{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}

module CostAnalysis.Analysis where

import Prelude hiding (sum)
import Control.Monad.RWS
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T
import Data.Maybe(maybeToList, fromMaybe)
import Data.Function(on)
import Lens.Micro.Platform

import Primitive(Id)
import Ast hiding (CostAnnotation)
import CostAnalysis.Solving (solve)
import CostAnalysis.ProveMonad
import CostAnalysis.Constraint hiding (and)
import SourceError
import CostAnalysis.Rules
import Control.Monad.Except (liftEither)
import CostAnalysis.Deriv
import CostAnalysis.Coeff
import Typing.Type
import CostAnalysis.RsrcAnn (RsrcAnn, RsrcSignature,
                             FunRsrcAnn(..), annLikeConstEq,
                             annLikeConstLe, PointWiseOp,
                             opCoeffs, annLikeGeZero)
import CostAnalysis.Potential(symbolicCost, cOptimize, Potential (cExternal))
import CostAnalysis.Potential.Kind (fromKind)
import Data.List (sortBy, groupBy)
import Data.Ord (comparing)




analyzeModule :: ProofEnv -> PositionedModule
  -> IO (Either SourceError (Derivation, RsrcSignature, Either [Constraint] (Solution, PotFnMap)))
analyzeModule env mod = do
  let state = ProofState M.empty [] [] 0 0 [] [] M.empty (fromKind $ fallbackPot mod)
  (result, state', solution) <- runProof env state (analyzeModule' mod)
  let deriv = T.Node (ProgRuleApp mod) (state'^.fnDerivs)
  case result of
    Left (DerivErr srcErr) -> return (Left srcErr)
    Left (UnsatErr core) -> return (Right (deriv, state'^.sig, Left core))
    Right potFns -> return (Right (deriv, state'^.sig, Right (solution, potFns)))

type PotFnMap = Map PotentialKind (Potential, RsrcAnn)

analyzeModule' :: PositionedModule -> ProveMonad PotFnMap
analyzeModule' mod = do
  potentials <- instantiatePotFns . groupFnsByPotential $ mod
  incr <- view incremental
  if incr then
    mapM_ (analyzeBindingGroup mod potentials) (mutRecGroups mod)
  else
    analyzeBindingGroup mod potentials (concat $ mutRecGroups mod)
  return potentials

fallbackPot mod = fromMaybe Logarithmic (modPotential mod) 

groupFnsByPotential :: PositionedModule -> [(PotentialKind, [FunDef Positioned])]
groupFnsByPotential mod = map (\l -> (fst . head $ l, map snd l)) . groupBy ((==) `on` fst) . sortBy (comparing fst) $ fnsWithPot
  where fnsWithPot = map (\fn -> (getPot fn, fn)) (M.elems . defs $ mod)
        getPot fn = case (tfPotential . funAnn) fn of
                      Nothing -> fallbackPot mod
                      Just pot -> pot

instantiatePotFns :: [(PotentialKind, [FunDef Positioned])] -> ProveMonad PotFnMap
instantiatePotFns groups = M.fromList <$> mapM go groups
  where go (kind, fns) = do
          args <- liftEither $ argsForRHS fns
          let pot = fromKind kind
          ann <- defaultAnn' pot "Q'" "fn" args
          return (kind, (pot, ann))

analyzeBindingGroup :: PositionedModule -> PotFnMap -> [Id]  -> ProveMonad ()
analyzeBindingGroup mod pots fns = do
  derivs <- mapM (analyzeFn mod pots . (defs mod M.!)) fns
  fnDerivs %= (++derivs)
  solution <- solve fns
  addSigCs fns solution
  tell solution

analyzeFn :: PositionedModule -> PotFnMap -> PositionedFunDef -> ProveMonad Derivation
analyzeFn mod pots fn = do
  let kind = fromMaybe (fallbackPot mod) $ tfPotential $ funAnn fn
  let pot = pots M.! kind
  potential .= fst pot
  createAnn kind (snd pot) fn
  analyzeFn' fn
         
createAnn :: PotentialKind -> RsrcAnn -> PositionedFunDef -> ProveMonad ()
createAnn kind rhs def@(Fn fn _ _) = do
  let rhs' = case tfCostAnn $ funAnn def of
        Just (Cost True _) -> Nothing
        _notWorstCase -> Just rhs
  ann <- genFunRsrcAnn kind rhs' def
  sig %= M.insert fn ann

analyzeFn' :: PositionedFunDef -> ProveMonad Derivation
analyzeFn' def@(FunDef funAnn fnId _ body) = do
  pot <- use potential
  mode <- view analysisMode
  
  case mode of
    CheckCoefficients -> case tfCostAnn funAnn of
      Just Coeffs {..} -> coeffsMatchAnnotation fnId (caWithCost, caWithoutCost)
      Just (Cost True cost) -> coeffsMatchAnnotation fnId ((cost, M.empty) , Nothing)
      _noCoeff -> errorFrom (SynExpr body) "Missing resource coefficient annotation for check-coeffs mode."
    CheckCost -> case tfCostAnn funAnn of
      Just Cost {..} -> cmpCostWithAnn annLikeConstEq fnId costCoeffs
      _noCost -> errorFrom (SynExpr body) "Missing cost annotation for check-cost mode."
    ImproveCost -> case tfCostAnn funAnn of
      Just Cost {..} -> do
        cmpCostWithAnn annLikeConstLe fnId costCoeffs
        addSimpleCostOptimization fnId
      noCost_ -> errorFrom (SynExpr body) "Missing cost annotation for improve-cost mode."
    Infer -> do
      s <- use sig
      tellCs (cExternal pot $ s M.! fnId)
      addFullCostOptimization fnId
  proveFun def


type CostComparision = PointWiseOp -> Map CoeffIdx Rational -> [Constraint]

cmpCostWithAnn :: CostComparision -> Id -> Map CoeffIdx Rational -> ProveMonad ()
cmpCostWithAnn cmp fn costAnn = do
  ann <- (M.! fn) <$> use sig
  let cost = symbolicCost (withCost ann)
  tellSigCs $ annLikeGeZero cost
  tellSigCs $ cmp cost costAnn

coeffsMatchAnnotation :: Id -> (Ast.FunRsrcAnn, Maybe Ast.FunRsrcAnn) -> ProveMonad ()
coeffsMatchAnnotation fn (annWithCost, annWithoutCost) = do
  ann <- (M.! fn) <$> use sig
  let (p, p') = withoutCost ann
  let (q, q') = withCost ann
  tellSigCs (annLikeConstEq q $ fst annWithCost)
  tellSigCs (annLikeConstEq q' $ snd annWithCost)
  tellSigCs . concat . maybeToList $ (annLikeConstEq p . fst <$> annWithoutCost)
  tellSigCs . concat . maybeToList $ (annLikeConstEq p' . snd <$> annWithoutCost)

addSimpleCostOptimization :: Id -> ProveMonad ()
addSimpleCostOptimization fn = do
  ann <- (M.! fn) <$> use sig
  let cost = symbolicCost (withCost ann)
  let costTerm = sum $ M.elems (opCoeffs cost)
  optiTargets %= (costTerm:)

  
addFullCostOptimization :: Id -> ProveMonad ()
addFullCostOptimization fn = do
  pot <- use potential
  ann <- (M.! fn) <$> use sig
  let (q, q') = withCost ann
  let costTerm = cOptimize pot q q'
  optiTargets %= (costTerm:)
  

genFunRsrcAnn :: PotentialKind -> Maybe RsrcAnn -> PositionedFunDef -> ProveMonad CostAnalysis.RsrcAnn.FunRsrcAnn
genFunRsrcAnn kind rhs fun = do
  let (argsFrom, argsTo) = ctxFromFn fun
  to <- case rhs of
    Just ann -> return ann
    Nothing -> emptyAnn "Q'" "fn" argsTo
  from <- defaultAnn "Q" "fn" argsFrom
  fromCf <- defaultAnn "P" "fn cf" argsFrom
  toCf <- defaultAnn "P'" "fn cf" argsTo
  let wc = case  (tfCostAnn . funAnn) fun of
        Just (Cost {worstCase,..}) -> worstCase
        _coeffs -> False
  return $ FunRsrcAnn (from, to) (fromCf, toCf) kind wc

  
addSigCs :: [Id] -> Solution -> ProveMonad ()
addSigCs fns solution = do
  sig' <- (`M.restrictKeys` S.fromList fns) <$> use sig
  let cs = concatMap go (getCoeffs sig')
  sigCs %= (++cs)
  where go coeff = eq (CoeffTerm coeff) (ConstTerm (solution M.! coeff))


-- TODO this breaks RandSplayTree.delete because splay max returns a tuple not a single tree.  
argsForRHS :: [FunDef Positioned] -> Either ProofErr [(Id, Type)]
argsForRHS fns = if sameLength args then
                   case args of
                     [] -> Right []
                     arg:args -> Right arg
                 else
                   Left . DerivErr $ SourceError (tfLoc $ funAnn (head fns))
                   "Cost analysis requries all involved functions to have the same return type to guarantee a consistent potential function."
  where args = [ snd . ctxFromFn $ fn
               | fn <- fns,
                 hasPotential fn]
        sameLength l = and [length l1 == length l2
                           | l1 <- l, l2 <- l]

