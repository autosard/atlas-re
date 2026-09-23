module Syntax.ResourceExpression.Order
  ( resourceLe
  , computeStratifiedCosts
  )where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.MultiSet as MSet

import Syntax (Id, HasVars (..))
import Syntax.ResourceExpression
import Data.List (partition)
import qualified Syntax.FreeModule as FM
import Syntax.ResourceExpression.Inequality
import Control.Monad (replicateM)

-- | A canonical linear combination: Map of (Variable -> Coefficient) and a constant offset.
-- Represents: c + sum_{x} coeff(x) * x
data LinearCombo = LinearCombo 
  { coeffs :: M.Map Id Int
  , offset :: Int 
  } deriving (Show, Ord, Eq)


-- | Given two sums of SizeTerms representing (q_terms + c) and (p_terms + d),
-- returns:
-- 1. A Map representing the coefficient differences vector p = a - b
-- 2. The constant difference beta = d - c
diffSums :: SizeExpr -> SizeExpr -> (M.Map Id Rational, Rational)
diffSums s1 s2 = (p, beta)
  where
    allVars = freeVars s1 `S.union` freeVars s2 -- Assumes S is Data.Set
    p = M.fromSet (\x -> M.findWithDefault 0 (SVar x) s1
                    - M.findWithDefault 0 (SVar x) s2) allVars
    c = M.findWithDefault 0 SId s1
    d = M.findWithDefault 0 SId s2
    beta = d - c

-- | Checks if (sum qTerms) <= (sum pTerms) under the given guard constraints
-- using the dual certificate (v = 0 or v = 1).
sizeExprLe :: SizeGuardMatrix -> SizeExpr -> SizeExpr -> Bool
sizeExprLe (mA, b) qTerms pTerms =
  any checkCertificate (binaryLists numGuards)
  where
    binaryLists n = replicateM n [0, 1]
    -- Extract p = a - b and beta = d - c
    (pMap, beta) = diffSums qTerms pTerms
    vars         =
      S.toList $
      S.unions (map M.keysSet mA)
      `S.union` M.keysSet pMap
      
    -- 1. Setup our search space variables based on the constraints
    numGuards = length mA
    -- 2. Validation check for a specific v choice (zeroV or oneV)
    checkCertificate :: [Rational] -> Bool
    checkCertificate v = cond1 && cond2
      where
        -- Condition 1: A^T * v >= p
        cond1 = all checkVar vars
        checkVar x = 
          let px = M.findWithDefault 0 x pMap
              colSum = sum [ vi * M.findWithDefault 0 x guard 
                           | (vi, guard) <- zip v mA
                           ]
          in colSum >= px

        -- Condition 2: v^T * b <= beta 
        vDotB = sum [ vi * bi
                      | (vi, bi) <- zip v b
                      ]
        cond2 = vDotB <= beta

-- | Checks if resource term r1 <= r2 under the given guard constraints.
resourceLe :: SizeGuardMatrix -> ResourceTerm -> ResourceTerm -> Bool
-- resourceLe guards RTId (RTPhi _) = True
-- 1. Constant 1 Term (RTId) vs Sizes
-- RTId is treated semantically as the constant 1 size term: (SConst 1)
resourceLe guards RTId (RTSize s) = True
  --sizeSumLe guards [SConst 1] [s]
  
resourceLe guards (RTSize x) RTId = 
  sizeExprLe guards (FM.singleton (SVar x)) (FM.singleton SId)

-- 2. Pure Sizes (Linear Terms)
resourceLe guards (RTSize x) (RTSize y) = 
  sizeExprLe guards (FM.singleton (SVar x)) (FM.singleton (SVar y))

-- 3. Logarithmic Terms
resourceLe guards (RTLog qTerms) (RTLog pTerms) = 
  sizeExprLe guards qTerms pTerms

-- 4. Products  
resourceLe guards (RTProd qTerms) (RTProd pTerms) =
   all (uncurry (resourceLe guards)) (zip (MSet.toList qTerms) (MSet.toList pTerms))

resourceLe guards RTId (RTLog s) = FM.coeffSum s >= 2
-- 4. Logarithmic Terms vs Linear Terms (Asymptotic Dominance)
-- Logarithmic terms are always bounded by linear terms (e.g., log(x) <= x)
resourceLe _ (RTLog _) (RTSize _) = True
resourceLe _ (RTSize _) (RTLog _) = False

-- 5. Fallback for all other terms (RTPhi, RTBinoms, etc.)
-- These cannot be semantically compared beyond strict structural equivalence.
resourceLe _ r1 r2 = r1 == r2


-- | Assigns identical costs to terms that are incomparable or equivalent under resourceLe
computeStratifiedCosts :: SizeGuardMatrix -> Set ResourceTerm -> [(ResourceTerm, Int)]
computeStratifiedCosts g terms = go 1 (S.toList terms)
  where
    go :: Int -> [ResourceTerm] -> [(ResourceTerm, Int)]
    go _ [] = []
    go currentCost remaining =
      -- A term belongs to the current layer if NO OTHER remaining term is strictly smaller than it
      let (layer, nextRemaining) = partition (\x -> not (any (\y -> strictlyLess y x) remaining)) remaining
          assignedLayer = map (\term -> (term, currentCost)) layer
      in assignedLayer ++ go (currentCost + 1) nextRemaining

    -- x is strictly less than y if x <= y and NOT y <= x
    strictlyLess :: ResourceTerm -> ResourceTerm -> Bool
    strictlyLess x y = resourceLe g x y && not (resourceLe g y x)
