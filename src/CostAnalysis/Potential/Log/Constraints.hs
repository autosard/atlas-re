{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module CostAnalysis.Potential.Log.Constraints where

import Prelude hiding (exp, (!!))
import qualified Data.List as L
import qualified Data.Set as S
import Lens.Micro.Platform

import Primitive(Id)
import CostAnalysis.Potential.Log.Base
import CostAnalysis.RsrcAnn
import CostAnalysis.Constraint
import CostAnalysis.AnnIdxQuoter(mix)
import Typing.Type
import CostAnalysis.Coeff (constFactor, idxSum, facForVar, varsExcept, onlyVars, justConst)
import CostAnalysis.Potential (emptyAnn)
import Data.List.Extra (groupSort)

exp :: Id
exp = "e"

cConst :: Args
  -> RsrcAnn -> RsrcAnn -> [Constraint]
cConst potArgs q q'
  -- leaf 
  | (null . _args $ q) && (length . _args $ q') == 1 =
    eqSum (q!?[mix|2|]) [q'!?exp, q'!?[mix|2|]] 
    ++ concat [eqSum (q![mix|c|]) [q'!?[mix|exp^a,b|]
                            | a <- [0..c],
                              let b = c - a,
                              a + b == c]
                        | idx <- mixes q,
                          let c = constFactor idx,
                          c > 2]
    ++ concat [zero (q'!idx)
       | let qConsts = S.fromList $ (filter (>=2) . map constFactor) (mixes q),
         idx <- mixes q',
         idxSum idx `S.notMember` qConsts]

  -- node
  | (length . _args $ q) == 2 && (length . _args $ q') == 1 =
    let [x1, x2] = annVars q in
      eq (q!?x1) (q'!?exp) 
      ++ eq (q!?x2) (q'!?exp) 
      ++ eq (q!?[mix|x1^1|]) (q'!?exp) 
      ++ eq (q!?[mix|x2^1|]) (q'!?exp) 
      ++ concat [eq (q!?[mix|x1^a,x2^a,c|]) (q'!?[mix|exp^a,c|])
                | idx <- mixes q,
                  let a = facForVar idx x1,
                  a == facForVar idx x2,
                  let c = constFactor idx]
      ++ concat [zero (q![mix|x1^x,x2^y,c|]) 
                | idx <- mixes q,
                  let x = facForVar idx x1,
                  let y = facForVar idx x2,
                  let c = constFactor idx,
                  x /= y,
                  x + y + c > 1]
      ++ concat [zero (q'![mix|exp^a,c|]) 
                | idx <- mixes q',
                  let a = facForVar idx exp,
                  let c = constFactor idx,
                  [mix|x1^a,x2^a,c|] `S.notMember` (q^.coeffs)]
      

cMatch :: RsrcAnn -> RsrcAnn -> Id -> [(Id, Type)] -> (RsrcAnn, [Constraint])
cMatch q p x ys = cMatch' q p x (map fst ys')
  where ys' = filter (\(x, t) -> matchesTypes t types) ys

cMatch' :: RsrcAnn -> RsrcAnn -> Id -> [Id] -> (RsrcAnn, [Constraint])
-- leaf  
cMatch' q p x [] = extendAnn p $
  [(`eq` (q!y)) <$> def y | y <- L.delete x (annVars q)]
  ++ [(`eqSum` qs) <$> def [mix|_xs, c|]
     | ((xs, c), qs) <- sums]
  where sums = groupSort $
          ((S.empty, 2), q!x)
          : [((xs, c), q!idx) 
            | idx <- mixes q,
              let a = facForVar idx x,
              let b = constFactor idx,
              a > 0, b > 0,
              let c = a + b,
              c /= 2,
              let xs = varsExcept idx [x]]
-- node
cMatch' q r x [u, v] = extendAnn r $
  [(`eq` (q!x)) <$> def u,
   (`eq` (q!x)) <$> def v,
   (`eq` (q!x)) <$> def [mix|u^1|],
   (`eq` (q!x)) <$> def [mix|v^1|]]
  ++ [(`eq` (q!idx)) <$> def [mix|_xs,u^a,v^a,b|]
     | idx <- mixes q,
       let a = facForVar idx x,
       let b = constFactor idx,
       let xs = varsExcept idx [x]]
  ++ [(`eq` (q!y)) <$> def y | y <- L.delete x (annVars q)]
cMatch' _ _ x ys = error $ "x: " ++ show x ++ ", ys: " ++ show ys

cLetBinding :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBinding q p = extendAnn p $
  [(`eq` (q!x)) <$> def x  | x <- xs]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx (S.fromList xs)]
  where xs = annVars p

cLetBodyBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
cLetBodyBase q r p' = extendAnn r $
  [(`eq` (q!y)) <$> def y | y <- ys]
  ++ [(`eq` (q!idx)) <$> def idx
     | idx <- mixes q,
       onlyVars idx (S.fromList ys),
       (not . justConst) idx]
  ++ [(`eq` (p'!idx)) <$> def idx
     | idx <- mixes p',
       onlyVars idx S.empty]
  where ys = annVars r


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
       (not . S.null) xs', 
       c <- bRange potArgs]
  -- move const
  ++ [Eq (CoeffTerm (r![mix|2|])) (Sum [sub [p'![mix|2|], p![mix|2|]], CoeffTerm (q![mix|2|])])]
  ++ [le (p![mix|2|]) (q![mix|2|])]
  ++ [eq (r!y) (q!y) | y <- ys]
  ++ [eq (r![mix|x^d,e|]) (p'![mix|exp^d,e|])
     | d <- dRange potArgs, d /= 0, e <- _eRange]
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

