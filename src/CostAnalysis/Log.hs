{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module CostAnalysis.Log where

import qualified Data.Map as M
import Data.List(intercalate)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set(Set)
import Prelude hiding ((!!), (^), exp)
import qualified Prelude as P((^))
import Data.Text(Text)
import qualified Data.Text as T

import Primitive(Id)
import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Rules ( RuleArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.RsrcAnn
import CostAnalysis.Potential(Potential (Potential), GroundPot)       
import CostAnalysis.Optimization
import Typing.Type


data LogPotArgs = LogPotArgs {
  aRange :: ![Int],
  bRange :: ![Int],
  dRange :: ![Int],
  eRange :: ![Int],
  eRangeNeg :: ![Int]}

exp :: Id
exp = "e"

types = [TreeType]

combi :: LogPotArgs -> [Id] -> [Set Factor]
combi args xs = map S.fromList $
  combi' args [[Const c | c > 0] | c <- bRange args] xs

varCombi :: LogPotArgs -> [Id] -> [Set Factor]
varCombi args xs = map S.fromList $ combi' args [[]] xs


combi' :: LogPotArgs -> [[Factor]] -> [Id] -> [[Factor]]
combi' args z [] = z
combi' args z (x:xs) = [if a > 0 then x^a:y else y
                       | a <- aRange args, y <- combi' args z xs]


rsrcAnn :: LogPotArgs
  -> Int -> Text -> [(Id, Type)] -> GroundAnn
rsrcAnn potArgs id label args = RsrcAnn args' $ M.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [(Pure x, AnnCoeff id label "log" (Pure x)) | (x,i) <- zip vars [1..]]
        logCoeffs = map ((\idx -> (idx, AnnCoeff id label "log" idx)) . Mixed) $ combi potArgs vars
        args' = filter (\(x, t) -> matchesTypes t types) args
        vars = map fst args'


forAllCombinations :: LogPotArgs
  -> Bool -> [Id] -> Id -> Int -> Text -> [(Id, Type)] -> (AnnArray GroundAnn, Int)
forAllCombinations args neg xs x id label ys = (array, nextId)
  where idxs = [S.unions [xIdx, xsIdx, cIdx]
               | xIdx <- varCombi args [x], (not . S.null) xIdx,
                 xsIdx <- varCombi args xs, (not . S.null) xsIdx,
                 cIdx <- combi args []]
        nextId = id + length idxs
        arrIdx = Mixed . S.fromList
        printIdx idx = "(" ++ intercalate "," (map show (S.toAscList idx)) ++ ")"
        label' l idx = T.concat [l, "_", T.pack $ printIdx idx]
        array = M.fromList [(idx, rsrcAnn args id (label' label idx) ys)
                           | (idx, id) <- zip idxs [id..]]


elems :: AnnArray GroundAnn -> [GroundAnn]
elems = M.elems

eqExceptConst :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
eqExceptConst potArgs q p = let qs = annVars q in
  [Eq (q!x) (p!x) | x <- qs]
  ++ [Eq (q!idx) (p!idx)
     | idx <- combi potArgs qs, idx /= [mix|2|]]
       
cPlusConst :: LogPotArgs
  -> GroundAnn -> GroundAnn -> Rational -> [Constraint]
cPlusConst potArgs q p c = let qs = args q in
  EqPlusConst (q![mix|2|]) (p![mix|2|]) c :
  eqExceptConst potArgs q p

cMinusVar :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cMinusVar potArgs q p = let qs = args q in 
  EqMinusVar (q![mix|2|]) (p![mix|2|]) :
  eqExceptConst potArgs q p
  
cPlusMulti :: LogPotArgs
  -> GroundAnn -> GroundAnn -> GroundAnn -> [Constraint]
cPlusMulti potArgs q p r = let xs = annVars q
                               ys = annVars p in 
  [EqPlusMulti (q!x) (p!y) (r!y) | (x,y) <- zip xs ys]
  ++ [EqPlusMulti (q!idxQ) (p!idxP) (r!idxP)
     | (idxQ, idxP) <- zip (combi potArgs xs) (combi potArgs ys)]

cEq :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cEq potArgs q q'
  | (null . args $ q) && (length . args $ q') == 1 =
    EqSum (q![mix|2|]) [q'!exp, q'![mix|2|]] :
    [EqSum (q![mix|2|]) [q'![mix|exp^a,b|]
                            | a <- aRange potArgs,
                              b <- bRange potArgs, a + b == c]
                        | c <- bRange potArgs, c > 2]
  | (length . args $ q) == 2 && (length . args $ q') == 1 =
    let [x1, x2] = annVars q in
      Eq (q!x1) (q'!exp) :
      Eq (q!x2) (q'!exp) :
      Eq (q![mix|x1^1|]) (q'!exp) :
      Eq (q![mix|x2^1|]) (q'!exp) :
      [Eq (q![mix|x1^a,x2^a,c|]) (q'![mix|exp^a,c|])
      | a <- aRange potArgs,
        c <- bRange potArgs]
  | (length . args $ q) == 1 && (length .args $ q') == 1 =
    let [x] = annVars q in 
      Eq (q!x) (q'!exp) :
      [Eq (q!idxQ) (q'!idxQ')
      | (idxQ, idxQ') <- zip (combi potArgs [x]) (combi potArgs [exp])]

cMatch :: LogPotArgs ->
  GroundAnn -> GroundAnn -> Id -> [(Id, Type)] -> [Constraint]
cMatch potArgs q p x ys = cMatch' potArgs q p x (map fst ys')
  where ys' = filter (\(x, t) -> matchesTypes t types) ys
  
{- HLINT ignore cMatch' "Move guards forward" -}
cMatch' :: LogPotArgs ->
  GroundAnn -> GroundAnn -> Id -> [Id] -> [Constraint]
cMatch' potArgs q p x [] =
  let nonMatchVars = L.delete x (annVars q) in
      [Eq (q!y) (p!y) | y <- nonMatchVars]
      ++ [EqSum (p![mix|2|]) [q![mix|2|], q!x]]
      ++ [EqSum (p!idx) [q![mix|_xs,x^a,b|]
                        | a <- aRange potArgs,
                          b <- bRange potArgs,
                          a + b == c]
         | xs <- varCombi potArgs nonMatchVars,
           c <- bRange potArgs,
           let idx = [mix|_xs,c|],
           idx /= [mix|2|]]
cMatch' potArgs q r x [u, v] =
  let nonMatchVars = L.delete x (annVars q) in
    Eq (r!u) (q!x) :
    Eq (r!v) (q!x) :
    Eq (r![mix|u^1|]) (q!x) :
    Eq (r![mix|v^1|]) (q!x) :
    [Eq (r![mix|_xs,u^a,v^a,b|]) (q![mix|_xs,x^a,b|])
    | xs <- varCombi potArgs nonMatchVars,
      a <- aRange potArgs,
      b <- bRange potArgs]
    ++ [Eq (q!y) (r!y) | y <- nonMatchVars]
cMatch' _ _ _ x ys = error $ "xs: " ++ show x ++ ", ys: " ++ show ys

cLetBase :: LogPotArgs
  -> GroundAnn -> GroundAnn -> GroundAnn -> GroundAnn -> [Constraint]
cLetBase potArgs q p r p' = let xs = annVars p 
                                ys = annVars r in
  [Eq (r![mix|c|]) (p'![mix|c|]) | c <- bRange potArgs]
  ++ [Eq (r!y) (q!y) | y <- ys]
  ++ [Eq (p!x) (q!x) | x <- xs]
  ++ [Eq (p![mix|_xs',c|]) (q![mix|_xs',c|])
     | xs' <- varCombi potArgs xs,
       c <- bRange potArgs]
  ++ [Eq (q![mix|_ys', c|]) (r![mix|_ys',c|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys', 
       c <- bRange potArgs]

cLet :: LogPotArgs
  -> Bool -> GroundAnn -> GroundAnn
  -> GroundAnn -> AnnArray GroundAnn
  -> AnnArray GroundAnn -> GroundAnn
  -> Id -> [Constraint]
cLet potArgs neg q p p' ps ps' r x = let xs = annVars p
                                         ys = L.delete x (annVars r) 
                                         _eRange = if neg then
                                           eRangeNeg potArgs
                                           else eRange potArgs in
  Eq (r!x) (p'!exp) :
  [Eq (p!x) (q!x) | x <- xs]
  ++ [Eq (p![mix|_xs',c|]) (q![mix|_xs',c|])
     | xs' <- varCombi potArgs xs,
       c <- bRange potArgs]
  ++ [Eq (r!y) (q!y) | y <- ys]
  ++ [Eq (r![mix|x^d,e|]) (p'![mix|exp^d,e|])
     | d <- dRange potArgs, e <- _eRange]
  ++ [Eq (r![mix|_ys',c|]) (q![mix|_ys', c|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys', 
       c <- bRange potArgs]
  ++ [EqSum (q![mix|_xs',_ys',c|]) [ps!![mix|_ys',x^d,e|]![mix|_xs',c|]
                                   | d <- dRange potArgs,
                                     d /= 0,
                                     e <- _eRange]
                                     -- let ce = c + max (-e) 0] check wether is even can work
     | xs' <- varCombi potArgs xs,
       (not .S.null) xs',
       ys' <- varCombi potArgs ys,
       (not .S.null) ys',
       c <- bRange potArgs]
  ++ [Eq (r![mix|_ys',x^d,e|]) (ps'!![mix|_ys',x^d,e|]![mix|exp^d,ePos|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0]
  ++ [Zero (ps'!![mix|_ys',x^d,e|]![mix|exp^d',e'|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0,
       d' <- dRange potArgs,
       e' <- _eRange,
       (d', e') /= (d, ePos)]
  ++ [GeSum [ps!![mix|_ys',x^d,e|]![mix|_xs',c|]
            | xs' <- varCombi potArgs xs,
              c <- bRange potArgs]
       (ps'!![mix|_ys',x^d,e|]![mix|exp^d,ePos|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0]
  ++ [Impl (NotZero (ps!![mix|_ys',x^d,e|]![mix|_xs',c|]))
      (Le (ps'!![mix|_ys',x^d,e|]![mix|exp^d,ePos|])
       (ps!![mix|_ys',x^d,e|]![mix|_xs',c|]))
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       xs' <- varCombi potArgs xs,
       (not . S.null) xs',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0,
       c <- bRange potArgs]           

cWeakenVar :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cWeakenVar potArgs q r = let xs = annVars r in
  [Eq (r!x) (q!x) | x <- xs]
  ++ [Eq (r![mix|_xs',b|]) (q![mix|_xs',b|])
     | xs' <- varCombi potArgs xs,
       b <- bRange potArgs]

-- TODO
cWeaken :: LogPotArgs ->
  [RuleArg] -> GroundAnn -> GroundAnn
  -> GroundAnn -> GroundAnn -> [Constraint]
cWeaken args ruleArgs q q' p p' = []


rankDifference :: GroundAnn -> GroundAnn -> OptiMonad Target
rankDifference q q' = do
  target <- freshCoeff
  (ds, diffs) <- bindToCoeffs (diff (q'!("e" :: Id))) (annVars q)
  let sum = EqSum target ds
  return (target, sum:diffs)
  where diff :: Coeff -> Coeff -> Id -> Constraint
        diff rankQ' d x = EqSub d [q!x, rankQ']


weightedNonRankDifference :: LogPotArgs -> GroundAnn -> GroundAnn -> OptiMonad Target
weightedNonRankDifference potArgs q q' = do
  target <- freshCoeff
  (ds, diffs) <- bindToCoeffs (\coeff (p, p', _) -> EqSub coeff [p, p']) pairs
  (ws, weightedDiffs) <- bindToCoeffs (\coeff (d, (_, _, (a,b))) -> EqMultConst coeff d (w a b)) (zip ds pairs)
  let sum = EqSum target ws
  return (target, sum:(diffs ++ weightedDiffs))
  where pairs = [(q![mix|x^a,b|], q'![mix|y^a,b|], (a,b))
                | a <- aRange potArgs,
                  b <- bRange potArgs,
                  (a, b) /= (0, 2),
                  let x = annVar q,
                  let y = annVar q']
        annVar p = case annVars p of
                     [x] -> x
                     _multiArg -> error "Index weight is only defined for annotations of length 1."
        w :: Int -> Int -> Rational
        w 0 2 = 0
        w a b = fromIntegral (a + (b+1) P.^ 2) P.^ 2
                       
constantDifference :: GroundAnn -> GroundAnn -> OptiMonad Target
constantDifference q q' = do
  target <- freshCoeff
  let diff = EqSub target [q![mix|2|], q'![mix|2|]]
  return (target, [diff])                                     

absoluteValue :: LogPotArgs -> GroundAnn -> OptiMonad Target
absoluteValue potArgs q = do
  target <- freshCoeff
  let sum = EqSum target [q!idx | idx <- combi potArgs (annVars q)]
  return (target, [sum])
  
cOptimize :: LogPotArgs ->
  GroundAnn -> GroundAnn -> OptiMonad Target
cOptimize potArgs q q' = do
  target <- freshCoeff
  (subTargets, cs) <- unzip <$> sequence [
        rankDifference q q',
        weightedNonRankDifference potArgs q q',
        constantDifference q q',
        absoluteValue potArgs q]
  (weightedSubTargets, csWeighted) <- bindToCoeffs (\coeff (target, w) -> EqMultConst coeff target w) $ zip subTargets [16127, 997, 97, 2]
  let sum = EqSum target weightedSubTargets
  return (target, sum:concat cs ++ csWeighted)

-- TODO accept arguments to be printed as well. 
-- printPot :: LogPotArgs
--   -> GroundAnn -> String
-- printPot args qs@(GroundAnn len _) = rankCoeffs ++ " " ++ logCoeffs 
--   where rankCoeffs = intercalate " + " [_printCoeff (qs![x]) ++ "rk(t)" | x <- [1..len]]
--         logCoeffs = intercalate " + " $ map (\idx -> _printCoeff (qs!idx) ++ printLog idx) (abIdx args len)
--         _printCoeff q = case printCoeff q of
--           "0" -> ""
--           s -> s
--         printLog :: [Int] -> String
--         printLog xs = "log(" ++ intercalate " + " (map show xs) ++ ")"

logPot :: LogPotArgs -> GroundPot
logPot args = Potential
  types
  (rsrcAnn args)
  (forAllCombinations args)
  elems
  (cPlusConst args)
  (cMinusVar args)
  (cPlusMulti args)
  (cEq args)
  (cMatch args)
  (cLetBase args)
  (cLet args)
  (cWeakenVar args)
  (cWeaken args)
  (cOptimize args)
  --(printPot args)
