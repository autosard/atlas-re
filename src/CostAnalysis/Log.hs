{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module CostAnalysis.Log where

import qualified Data.Map as M
import Data.List(delete, intercalate)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set(Set)
import Prelude hiding ((!!), (^), exp)


import CostAnalysis.AnnIdxQuoter(mix)
import CostAnalysis.Rules

import Data.Text(Text)

import CostAnalysis.Potential(GroundAnn,
                              Constraint(..),
                              Coeff(Unknown), (!),
                              CoeffIdx(..),
                              AnnArray, printCoeff, GroundPot,
                              Potential (Potential),
                              Factor(..),
                              (^),
                              (!!),
                              RsrcAnn(..))
import qualified Data.Text as T
import Primitive(Id)

data LogPotArgs = LogPotArgs {
  aRange :: ![Int],
  bRange :: ![Int],
  dRange :: ![Int],
  eRange :: ![Int],
  eRangeNeg :: ![Int]}

--aRange = [1, 0]
--bRange = [0, 2]
--dRange = aRange
--eRange = bRange
--eRangeNeg = -1 : eRange
  
-- abIdx :: LogPotArgs
--   -> Int -> [[Int]]
-- abIdx args 0 = [[x] | x <- bRange args]
-- abIdx args n = [x:y | x <- aRange args, y <- abIdx args (n-1)]

-- aIdx :: LogPotArgs
--   -> Int -> [[Int]]
-- aIdx args 1 = [[x] | x <- aRange args]
-- aIdx args n
--   | n <= 0 = [[]]
--   | otherwise = [x:y | x <- aRange args, y <- aIdx args (n-1)]
exp :: Id
exp = "e"

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
  -> Int -> Text -> [Id] -> GroundAnn
rsrcAnn potArgs id label args = RsrcAnn args $ M.fromList (rankCoeffs ++ logCoeffs)
  where rankCoeffs = [(Pure x, Unknown id label "log" (Pure x)) | (x,i) <- zip args [1..]]
        logCoeffs = map ((\idx -> (idx, Unknown id label "log" idx)) . Mixed) $ combi potArgs args


forAllCombinations :: LogPotArgs
  -> Bool -> [Id] -> Id -> Int -> Text -> [Id] -> (AnnArray GroundAnn, Int)
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
eqExceptConst potArgs q p = let qs = args q in
  [Eq (q!x) (p!x) | x <- qs]
  ++ [Eq (q!idx) (p!idx)
     | idx <- combi potArgs qs, idx /= [mix|2|]]
       
cPlusConst :: LogPotArgs
  -> GroundAnn -> GroundAnn -> Rational -> [Constraint]
cPlusConst potArgs q p c = let qs = args q in
  EqPlusConst (q![mix|2|]) (p![mix|2|]) c :
  eqExceptConst potArgs q p

cMinusConst :: LogPotArgs
  -> GroundAnn -> GroundAnn -> Rational -> [Constraint]
cMinusConst potArgs q p c = let qs = args q in
  EqMinusConst (q![mix|2|]) (p![mix|2|]) c :
  eqExceptConst potArgs q p

cMinusVar :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cMinusVar potArgs q p = let qs = args q in 
  EqMinusVar (q![mix|2|]) (p![mix|2|]) :
  eqExceptConst potArgs q p
  
cPlusMulti :: LogPotArgs
  -> GroundAnn -> GroundAnn -> GroundAnn -> [Constraint]
cPlusMulti potArgs q p r = let qs = args q in 
  [EqPlusMulti (q!x) (p!x) (r!x) | x <- qs]
  ++ [EqPlusMulti (q!idx) (p!idx) (r!idx)
     | idx <- combi potArgs qs]

cLeaf :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cLeaf potArgs q q' = 
  EqSum (q![mix|2|]) [q'!exp, q'![mix|2|]] :
  [EqSum (q![mix|2|]) [q'![mix|exp^a,b|]
                 | a <- aRange potArgs,
                   b <- bRange potArgs, a + b == c]
  | c <- bRange potArgs, c > 2]

cNode :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cNode potArgs q q' = let [x1, x2] = args q in
  Eq (q!x1) (q'!exp) :
  Eq (q!x2) (q'!exp) :
  Eq (q![mix|x1^1|]) (q'!exp) :
  Eq (q![mix|x2^1|]) (q'!exp) :
  [Eq (q![mix|x1^a,x2^a,c|]) (q'![mix|exp^a,c|])
  | a <- aRange potArgs,
    c <- bRange potArgs]

cPair :: LogPotArgs
  -> GroundAnn -> GroundAnn -> [Constraint]
cPair potArgs q q' = let [x] = args q in 
  Eq (q!x) (q'!exp) :
  [Eq (q!idxQ) (q'!idxQ')
  | (idxQ, idxQ') <- zip (combi potArgs [x]) (combi potArgs [exp])]

{- HLINT ignore cMatchLeaf "Move guards forward" -}
cMatchLeaf :: LogPotArgs ->
  GroundAnn -> GroundAnn -> Id -> [Constraint]
cMatchLeaf potArgs q p t = let nonMatchVars = L.delete t (args q) in
  [Eq (q!y) (p!y) | y <- nonMatchVars]
  ++ [EqSum (p![mix|2|]) [q![mix|2|], q!t]]
  ++ [EqSum (p!idx) [q![mix|_xs,t^a,b|]
                            | a <- aRange potArgs,
                              b <- bRange potArgs,
                              a + b == c]
     | xs <- varCombi potArgs nonMatchVars,
       c <- bRange potArgs,
       let idx = [mix|_xs,c|],
       idx /= [mix|2|]]

cMatchNode :: LogPotArgs
  -> GroundAnn -> GroundAnn -> Id -> Id -> Id -> [Constraint]
cMatchNode potArgs q r t u v = let nonMatchVars = L.delete t (args q) in
  Eq (r!u) (q!t) :
  Eq (r!v) (q!t) :
  Eq (r![mix|u^1|]) (q!t) :
  Eq (r![mix|v^1|]) (q!t) :
  [Eq (r![mix|_xs,u^a,v^a,b|]) (q![mix|_xs,t^a,b|])
  | xs <- varCombi potArgs nonMatchVars,
    a <- aRange potArgs,
    b <- bRange potArgs]
  ++ [Eq (q!y) (r!y) | y <- nonMatchVars]

cLetBase :: LogPotArgs
  -> GroundAnn -> GroundAnn -> GroundAnn -> GroundAnn -> [Constraint]
cLetBase potArgs q p r p' = let xs = args p 
                                ys = args r in
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
cLet potArgs neg q p p' ps ps' r x = let xs = args p
                                         ys = L.delete x (args r) 
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
     | d <- aRange potArgs, e <- _eRange]
  ++ [Eq (r![mix|_ys',c|]) (q![mix|_ys', c|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys', 
       c <- bRange potArgs]
  ++ [EqSum (q![mix|_xs',_ys',c|]) [ps!![mix|_ys',x^d,e|]![mix|_xs',ce|]
                                   | d <- dRange potArgs,
                                     d /= 0,
                                     e <- _eRange,
                                     let ce = c + max (-e) 0]
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
cWeakenVar potArgs q r = let xs = args r in
  [Eq (r!x) (q!x) | x <- xs]
  ++ [Eq (r![mix|_xs',b|]) (q![mix|_xs',b|])
     | xs' <- varCombi potArgs xs,
       b <- bRange potArgs]

cWeaken :: LogPotArgs ->
  [RuleArg] -> GroundAnn -> GroundAnn
  -> GroundAnn -> GroundAnn -> [Constraint]
cWeaken args ruleArgs q q' p p' = []


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

-- logPot :: LogPotArgs -> GroundPot
-- logPot args = Potential
--   (rsrcAnn args)
--   (enumAnn args)
--   (forAllCombinations args)
--   elems
--   annLen
--   (cPlusConst args)
--   (cMinusConst args)
--   (cMinusVar args)
--   (cPlusMulti args)
--   (cLeaf args)
--   (cNode args)
--   (cPair args)
--   (cMatchLeaf args)
--   (cMatchNode args)
--   (cLetBase args)
--   (cLet args)
--   (cWeakenVar args)
--   (cWeaken args)
--   (printPot args)
