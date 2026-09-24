module CostAnalysis.Subtyping (templLe) where

import Prelude hiding (sum)
import qualified Prelude as P (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Vector as V

import CostAnalysis.Template (Template(terms,(!?)))
import CostAnalysis.Coeff (HasCoeffs(..))
import Syntax.ResourceExpression
import CostAnalysis.Constraint
import CostAnalysis.ProveMonad
import CostAnalysis.Rules

import Syntax.ResourceExpression.Order ( resourceLe )
import Syntax.ResourceExpression.Axioms
import Syntax.ResourceExpression.Pattern ( findMatches, IneqPattern (..), SizeSubst, instResourceIneq ) 
import Data.Bifunctor (Bifunctor(first))
import Syntax.ResourceExpression.Inequality (ResourceIneq, SizeGuardMatrix, sizeConstraints )
import qualified Syntax.ResourceExpression.Inequality as ReIneq (ResourceIneq (LeZero))
import Lens.Micro.Platform (view)
import Text.Show.Pretty (ppShow)
import Primitive (dbg)

type LeMatrix = V.Vector (V.Vector Rational)

farkas :: LeMatrix -> V.Vector ArithExpr -> V.Vector ArithExpr -> ProveMonad [Formula]
farkas as ps qs | V.length ps == V.length qs = do
  let bs = replicate (length as) 0
  fs <- mapM (const freshVar) bs
  let fsPos = [ge f (ConstTerm 0) | f <- fs]
  let farkasA = [le (ps V.! i) (sum (qs V.! i:fas fs as i)) | i <- [0..length ps - 1]]
  let farkasB = [le (sum $ prods fs bs) (ConstTerm 0) | (not . all (== 0)) bs]
  return $ concatMap concat [fsPos, farkasA, farkasB]
  where prods fs as = zipWith prod2 fs (map ConstTerm as)
        fas fs as i = prods fs ([row V.! i | row <- V.toList as])

templLe :: (Template a, Template b, HasCoeffs a, HasCoeffs b) => Set SubArg -> [ResourceIneq] -> a -> b -> ProveMonad [Formula]
templLe subArgs rctx p q =
  let rctxBounds = lowerBounds rctx in do
    axs <- view axioms
    let ks = merge $
          [termOrderConstraints (sizeConstraints rctx) (terms p) | S.member Mono subArgs]
          ++ if S.member L2xy subArgs
             then map (instantiateAxiom rctxBounds (terms p)) axs
             else []
    farkas ks ps qs
  where ps = V.fromList . map CoeffTerm $ getCoeffs p
        qs = V.fromList $ [q!?t | t <- S.toList $ terms p]
  
merge :: [LeMatrix] -> LeMatrix
merge = V.concat 


termOrderConstraints :: SizeGuardMatrix -> S.Set ResourceTerm -> LeMatrix
termOrderConstraints guards terms = merge . catMaybes $
  [ compareTerms idxP idxQ
  | idxP <- termsList,
    idxQ <- termsList,
    idxP /= idxQ
  ]
  where 
    termsList = S.toList terms
    numTerms  = S.size terms

    compareTerms :: ResourceTerm -> ResourceTerm -> Maybe LeMatrix
    compareTerms t1 t2 = 
      if resourceLe guards t1 t2 then
        let i = S.findIndex t1 terms
            j = S.findIndex t2 terms 
        in Just (V.singleton $ V.generate numTerms (\k ->
                  if k == i then 1
                  else if k == j then -1
                  else 0))
      else Nothing

type LowerBounds = M.Map ResourceTerm Rational

lowerBounds :: [ResourceIneq] -> LowerBounds
lowerBounds = M.fromList . mapMaybe go 
  where go :: ResourceIneq -> Maybe (ResourceTerm, Rational)
        go (ReIneq.LeZero rt) = case M.toList rt of
          [(t, -1), (RTId, r)] -> Just (t, 1)
          [(RTId, r), (t, -1)] -> Just (t, 1)
          _                                      -> Nothing
                            
csIsValid :: LowerBounds -> ResourceIneq -> Bool
csIsValid bounds (ReIneq.LeZero re) =
  maybe False (\ts -> P.sum ts <= 0) $ traverse go (M.toList re)
  where
    go (RTId, r) = Just r
    go (t, r)
      | r < 0     = (* r) <$> bounds M.!? t
      | r == 0    = Just 0
      | otherwise = Nothing


-- | Instantiates all possible applications of an axiom over a set of ResourceTerms.
instantiateAxiom :: LowerBounds -> Set ResourceTerm -> AxiomSpec -> LeMatrix
instantiateAxiom rctx termsSet (AxiomSpec premises (LeZero conclusion)) =
  let premiseSet = S.fromList premises in 
    V.fromList . concatMap (buildRow premiseSet) $ findMatches conclusion (S.toList termsSet) 
  where
    
    numTerms = S.size termsSet

    -- For a successful combination of matched terms, generate the constraint row
    buildRow :: Set IneqPattern -> ([(ResourceTerm, Rational)], SizeSubst) -> [V.Vector Rational]
    buildRow premiseSet (matchedTerms, subst) =
      let instPremises = S.map (instResourceIneq subst) premiseSet in
      if all (csIsValid rctx) instPremises 
      then 
        let rowAssocs = map (first (`S.findIndex` termsSet)) matchedTerms
            rowMap    = M.fromListWith (+) rowAssocs 
        in [V.generate numTerms (\k -> M.findWithDefault 0 k rowMap)]
      else []



    
