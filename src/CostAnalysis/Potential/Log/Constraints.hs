{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Constraints where

import Prelude hiding (exp, (!!))
import qualified Data.List as L
import qualified Data.Set as S

import Primitive(Id)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import Typing.Type

exp :: Id
exp = "e"

eqExceptConst :: Args
  -> RsrcAnn -> RsrcAnn -> [Constraint]
eqExceptConst potArgs q p = let qs = annVars q in
  [eq (q!x) (p!x) | x <- qs]
  ++ [eq (q!idx) (p!idx)
     | idx <- combi potArgs qs, idx /= [mix|2|]]
       
cPlusConst :: Args
  -> RsrcAnn -> RsrcAnn -> Rational -> [Constraint]
cPlusConst potArgs q p c = let qs = args q in
  eqPlusConst (q![mix|2|]) (p![mix|2|]) c :
  eqExceptConst potArgs q p

cMinusVar :: Args
  -> RsrcAnn -> RsrcAnn -> Var -> [Constraint]
cMinusVar potArgs q p k = let qs = args q in 
  eqMinusVar (q![mix|2|]) (p![mix|2|]) k :
  eqExceptConst potArgs q p
  
cPlusMulti :: Args
  -> RsrcAnn -> RsrcAnn -> RsrcAnn -> Var -> [Constraint]
cPlusMulti potArgs q p r k = let xs = annVars q
                                 ys = annVars p in 
  [eqPlusMulti (q!x) (p!y) (r!y) k | (x,y) <- zip xs ys]
  ++ [eqPlusMulti (q!idxQ) (p!idxP) (r!idxP) k
     | (idxQ, idxP) <- zip (combi potArgs xs) (combi potArgs ys)]

cEq :: Args
  -> RsrcAnn -> RsrcAnn -> [Constraint]
cEq potArgs q q'
  | (null . args $ q) && (length . args $ q') == 1 =
    eqSum (q![mix|2|]) [q'!exp, q'![mix|2|]] :
    [eqSum (q![mix|2|]) [q'![mix|exp^a,b|]
                            | a <- aRange potArgs,
                              b <- bRange potArgs, a + b == c]
                        | c <- bRange potArgs, c > 2]
  | (length . args $ q) == 2 && (length . args $ q') == 1 =
    let [x1, x2] = annVars q in
      eq (q!x1) (q'!exp) :
      eq (q!x2) (q'!exp) :
      eq (q![mix|x1^1|]) (q'!exp) :
      eq (q![mix|x2^1|]) (q'!exp) :
      [eq (q![mix|x1^a,x2^a,c|]) (q'![mix|exp^a,c|])
      | a <- aRange potArgs,
        c <- bRange potArgs]
  | (length . args $ q) == (length .args $ q') =
      [eq (q!x) (q'!y) | (x, y) <- zip (annVars q) (annVars q') ]
      ++ [eq (q!idxQ) (q'!idxQ')
      | (idxQ, idxQ') <- zip (combi potArgs (annVars q)) (combi potArgs (annVars q'))]

cMatch :: Args ->
  RsrcAnn -> RsrcAnn -> Id -> [(Id, Type)] -> [Constraint]
cMatch potArgs q p x ys = cMatch' potArgs q p x (map fst ys')
  where ys' = filter (\(x, t) -> matchesTypes t types) ys
  
{- HLINT ignore cMatch' "Move guards forward" -}
cMatch' :: Args ->
  RsrcAnn -> RsrcAnn -> Id -> [Id] -> [Constraint]
cMatch' potArgs q p x [] =
  let nonMatchVars = L.delete x (annVars q) in
      [eq (q!y) (p!y) | y <- nonMatchVars]
      ++ [eqSum (p![mix|2|]) [q![mix|2|], q!x]]
      ++ [eqSum (p!idx) [q![mix|_xs,x^a,b|]
                        | a <- aRange potArgs,
                          b <- bRange potArgs,
                          a + b == c]
         | xs <- varCombi potArgs nonMatchVars,
           c <- bRange potArgs,
           let idx = [mix|_xs,c|],
           idx /= [mix|2|]]
cMatch' potArgs q r x [u, v] =
  let nonMatchVars = L.delete x (annVars q) in
    eq (r!u) (q!x) :
    eq (r!v) (q!x) :
    eq (r![mix|u^1|]) (q!x) :
    eq (r![mix|v^1|]) (q!x) :
    [eq (r![mix|_xs,u^a,v^a,b|]) (q![mix|_xs,x^a,b|])
    | xs <- varCombi potArgs nonMatchVars,
      a <- aRange potArgs,
      b <- bRange potArgs]
    ++ [eq (q!y) (r!y) | y <- nonMatchVars]
cMatch' _ _ _ x ys = error $ "xs: " ++ show x ++ ", ys: " ++ show ys

cLetBase :: Args
  -> RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> [Constraint]
cLetBase potArgs q p r p' = let xs = annVars p 
                                ys = annVars r in
  [eq (r![mix|c|]) (p'![mix|c|]) | c <- bRange potArgs]
  ++ [eq (r!y) (q!y) | y <- ys]
  ++ [eq (p!x) (q!x) | x <- xs]
  ++ [eq (p![mix|_xs',c|]) (q![mix|_xs',c|])
     | xs' <- varCombi potArgs xs,
       c <- bRange potArgs]
  ++ [eq (q![mix|_ys', c|]) (r![mix|_ys',c|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys', 
       c <- bRange potArgs]

cLet :: Args
  -> Bool -> RsrcAnn -> RsrcAnn -> RsrcAnn
  -> AnnArray -> AnnArray
  -> RsrcAnn
  -> Id -> [Constraint]
cLet potArgs neg q p p' ps ps' r x = let xs = annVars p
                                         ys = L.delete x (annVars r) 
                                         _eRange = if neg then
                                           eRangeNeg potArgs
                                           else eRange potArgs in
  eq (r!x) (p'!exp) :
  [eq (p!x) (q!x) | x <- xs]
  ++ [eq (p![mix|_xs',c|]) (q![mix|_xs',c|])
     | xs' <- varCombi potArgs xs,
       c <- bRange potArgs]
  ++ [eq (r!y) (q!y) | y <- ys]
  ++ [eq (r![mix|x^d,e|]) (p'![mix|exp^d,e|])
     | d <- dRange potArgs, e <- _eRange]
  ++ [eq (r![mix|_ys',c|]) (q![mix|_ys', c|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys', 
       c <- bRange potArgs]
  ++ [eqSum (q![mix|_xs',_ys',c|]) [ps!![mix|_ys',x^d,e|]![mix|_xs',c|]
                                   | d <- dRange potArgs,
                                     d /= 0,
                                     e <- _eRange]
                                     -- let ce = c + max (-e) 0] check wether is even can work
     | xs' <- varCombi potArgs xs,
       (not .S.null) xs',
       ys' <- varCombi potArgs ys,
       (not .S.null) ys',
       c <- bRange potArgs]
  ++ [eq (r![mix|_ys',x^d,e|]) (ps'!![mix|_ys',x^d,e|]![mix|exp^d,ePos|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0]
  ++ [zero (ps'!![mix|_ys',x^d,e|]![mix|exp^d',e'|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0,
       d' <- dRange potArgs,
       e' <- _eRange,
       (d', e') /= (d, ePos)]
  ++ [geSum [ps!![mix|_ys',x^d,e|]![mix|_xs',c|]
            | xs' <- varCombi potArgs xs,
              c <- bRange potArgs]
       (ps'!![mix|_ys',x^d,e|]![mix|exp^d,ePos|])
     | ys' <- varCombi potArgs ys,
       (not . S.null) ys',
       d <- dRange potArgs,
       d /= 0,
       e <- _eRange,
       let ePos = max e 0]
  ++ [Impl (notZero (ps!![mix|_ys',x^d,e|]![mix|_xs',c|]))
      (le (ps'!![mix|_ys',x^d,e|]![mix|exp^d,ePos|])
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

cWeakenVar :: Args
  -> RsrcAnn -> RsrcAnn -> [Constraint]
cWeakenVar potArgs q r = let xs = annVars r in
  [eq (r!x) (q!x) | x <- xs]
  ++ [eq (r![mix|_xs',b|]) (q![mix|_xs',b|])
     | xs' <- varCombi potArgs xs,
       b <- bRange potArgs]

