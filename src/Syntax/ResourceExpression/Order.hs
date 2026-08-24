module Syntax.ResourceExpression.Order
  ( GuardMatrix
  , resourceLe
  , computeStratifiedCosts
  )where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)

import Syntax (Id)
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size
import Data.List (partition)

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
diffSums :: SizeSum -> SizeSum -> (M.Map Id Int, Int)
diffSums (SizeSum qCoeffs c) (SizeSum pCoeffs d) = (p, beta)
  where
    -- p = a - b (where a is from q, b is from p)
    -- We match keys from both, using 0 as a default if a variable is missing on one side.
    allVars = M.keysSet qCoeffs `S.union` M.keysSet pCoeffs -- Assumes S is Data.Set
    p = M.fromSet (\var -> M.findWithDefault 0 var qCoeffs - M.findWithDefault 0 var pCoeffs) allVars
    
    -- beta = d - c
    beta = d - c

-- | Represents a list of guard constraints of the form (C-D)x <= 0.
-- Each Map in the list maps variable Ids to their coefficient in that constraint row.
type GuardMatrix = [M.Map Id Int]

-- | Checks if (sum qTerms) <= (sum pTerms) under the given guard constraints
-- using the dual certificate (v = 0 or v = 1).
sizeSumLe :: GuardMatrix -> SizeSum -> SizeSum -> Bool
sizeSumLe guards qTerms pTerms = checkCertificate zeroV || checkCertificate oneV
  where
    -- Extract p = a - b and beta = d - c
    (pMap, beta) = diffSums qTerms pTerms
    vars         = M.keys pMap
    
    -- 1. Setup our search space variables based on the constraints
    numGuards = length guards
    zeroV     = replicate numGuards 0
    oneV      = replicate numGuards 1

    -- 2. Validation check for a specific v choice (zeroV or oneV)
    checkCertificate :: [Int] -> Bool
    checkCertificate v = cond1 && cond2
      where
        -- Condition 1: (C-D)^T * v >= p
        -- For every variable x in our system, the combined constraint coeff must be >= p(x).
        cond1 = all checkVar vars
        checkVar x = 
          let px = M.findWithDefault 0 x pMap
              -- Compute column dot product: Sum of (v_i * coeff of x in guard_i)
              colSum = sum [ vi * M.findWithDefault 0 x guard 
                           | (vi, guard) <- zip v guards 
                           ]
          in colSum >= px

        -- Condition 2: p^T * 1 - v^T * (C-D) * 1 <= beta
        -- Because x >= 1, evaluating at 1 means summing the coefficients of each variable.
        pDot1 = sum (M.elems pMap)
        
        -- v^T * (C-D) * 1 is calculated by finding the row-sum of each guard, 
        -- multiplying by its corresponding v_i, and summing.
        vDotCD1 = sum [ vi * sum (M.elems guard) 
                      | (vi, guard) <- zip v guards 
                      ]
                      
        cond2 = (pDot1 - vDotCD1) <= beta

-- | Checks if resource term r1 <= r2 under the given guard constraints.
resourceLe :: GuardMatrix -> ResourceTerm -> ResourceTerm -> Bool


-- resourceLe guards RTId (RTPhi _) = True
-- 1. Constant 1 Term (RTId) vs Sizes
-- RTId is treated semantically as the constant 1 size term: (SConst 1)
resourceLe guards RTId (RTSize s) = True
  --sizeSumLe guards [SConst 1] [s]
  
resourceLe guards (RTSize s) RTId = 
  sizeSumLe guards (sizeVar s) (sizeConst 1)

-- 2. Pure Sizes (Linear Terms)
resourceLe guards (RTSize s1) (RTSize s2) = 
  sizeSumLe guards (sizeVar s1) (sizeVar s2)

-- 3. Logarithmic Terms
resourceLe guards (RTLog qTerms) (RTLog pTerms) = 
  sizeSumLe guards qTerms pTerms
  
resourceLe guards RTId (RTLog s) = coeffSum s >= 2
-- 4. Logarithmic Terms vs Linear Terms (Asymptotic Dominance)
-- Logarithmic terms are always bounded by linear terms (e.g., log(x) <= x)
resourceLe _ (RTLog _) (RTSize _) = True
resourceLe _ (RTSize _) (RTLog _) = False

-- 5. Fallback for all other terms (RTPhi, RTBinoms, etc.)
-- These cannot be semantically compared beyond strict structural equivalence.
resourceLe _ r1 r2 = r1 == r2


-- | Assigns identical costs to terms that are incomparable or equivalent under resourceLe
computeStratifiedCosts :: GuardMatrix -> Set ResourceTerm -> [(ResourceTerm, Int)]
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
