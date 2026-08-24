module CostAnalysis.Subtyping (templLe) where

import Prelude hiding (sum)
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import qualified Data.Vector as V

import CostAnalysis.Template (Template(terms,(!?)))
import CostAnalysis.Coeff (HasCoeffs(..))
import Syntax.ResourceExpression
import CostAnalysis.Constraint
import CostAnalysis.ProveMonad
import CostAnalysis.Rules

import Syntax.ResourceExpression.Order ( GuardMatrix, resourceLe )
import Syntax.ResourceExpression.Lemmas
import Syntax.ResourceExpression.Pattern ( findMatches ) 

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

templLe :: (Template a, Template b, HasCoeffs a, HasCoeffs b) => Set SubArg -> a -> b -> ProveMonad [Formula]
templLe subArgs p q = do
  let ks = merge $
        [termOrderConstraints [] (terms p) | S.member Mono subArgs]
        ++ [instantiateLemma logLemmaSpec (terms p) | S.member L2xy subArgs]
  farkas ks ps qs
  where ps = V.fromList . map CoeffTerm $ getCoeffs p
        qs = V.fromList $ [q!?t | t <- S.toList $ terms p]
  
merge :: [LeMatrix] -> LeMatrix
merge = V.concat 


termOrderConstraints :: GuardMatrix -> S.Set ResourceTerm -> LeMatrix
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

-- | Instantiates all possible applications of a lemma over a set of ResourceTerms.
instantiateLemma :: LemmaSpec -> S.Set ResourceTerm -> LeMatrix
instantiateLemma (LemmaSpec weightedPatterns d) termsSet = 
  V.fromList . concatMap buildRows $ findMatches patterns (S.toList termsSet) M.empty
  where
    patterns = map (\(WeightedPattern _ p) -> p) weightedPatterns
    numTerms = S.size termsSet
    iConst   = S.findIndex RTId termsSet

    -- For a successful combination of matched terms, generate the constraint row
    buildRows :: [ResourceTerm] -> [V.Vector Rational]
    buildRows matchedTerms = case mapM (`S.lookupIndex` termsSet) matchedTerms of
      Nothing -> [] -- Skip if some matched term is missing from our active template set
      Just indices ->
        let rowAssocs = (iConst, d) : zipWith (\idx (WeightedPattern coeff _) -> (idx, coeff)) indices weightedPatterns
            rowMap    = M.fromListWith (+) rowAssocs
        in [V.generate numTerms (\k -> M.findWithDefault 0 k rowMap)]



    
