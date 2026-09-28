-- | Plain-text rendering of resource terms, templates and constraints for
-- the proof viewer.
module CostAnalysis.PrettyProof.Format
  ( showRat
  , showSize
  , showTerm
  , showBound
  , showRScalarExpr
  , showPattern
  , ConstraintRow (..)
  , constraintRow
  , WeakeningVar (..)
  , weakeningVars
  , coeffIds
  ) where

import Data.List (intercalate, sortOn)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.MultiSet as MSet
import qualified Data.Set as S
import Data.Ratio (numerator, denominator)
import qualified Data.Text as T
import Control.Monad (foldM)

import CostAnalysis.Coeff (Coeff (..))
import CostAnalysis.Constraint (Formula (..), ArithExpr (..))
import Syntax.ResourceExpression
import Syntax.Pattern (Pattern (..))

--------------------------------------------------------------------------------
-- Numbers, sizes and terms
--------------------------------------------------------------------------------

showRat :: Rational -> String
showRat r
  | r < 0 = "−" ++ showRat (negate r)
  | denominator r == 1 = show (numerator r)
  | otherwise = case (numerator r, denominator r) of
      (1, 2) -> "½"
      (1, 3) -> "⅓"
      (2, 3) -> "⅔"
      (1, 4) -> "¼"
      (3, 4) -> "¾"
      (n, d) -> show n ++ "/" ++ show d

-- | Joins scaled summands into a signed sum. An empty body denotes a constant.
joinSigned :: [(Rational, String)] -> String
joinSigned = joinSignedWith " + " " − "

joinSignedWith :: String -> String -> [(Rational, String)] -> String
joinSignedWith _ _ [] = "0"
joinSignedWith plus minus (x : xs) = lead x ++ concatMap rest xs
  where
    lead (k, b)
      | k < 0 = "−" ++ scaled (abs k) b
      | otherwise = scaled k b
    rest (k, b)
      | k < 0 = minus ++ scaled (abs k) b
      | otherwise = plus ++ scaled k b
    scaled k "" = showRat k
    scaled 1 b = b
    scaled k b = showRat k ++ "·" ++ b

showSize :: SizeExpr -> String
showSize m = joinSignedWith "+" "−" $
  [(k, "|" ++ T.unpack x ++ "|") | (SVar x, k) <- M.toList m, k /= 0]
  ++ [(k, "") | Just k <- [M.lookup SId m], k /= 0]

showTerm :: ResourceTerm -> String
showTerm (RTSize x) = "|" ++ T.unpack x ++ "|"
showTerm (RTLog s) = "log(" ++ showSize s ++ ")"
showTerm (RTPhi x) = "𝜙(" ++ T.unpack x ++ ")"
showTerm (RTBinom s k) = "binom(" ++ showSize s ++ ", " ++ show k ++ ")"
showTerm (RTProd ts) = intercalate "·" (map showTerm (MSet.toList ts))
showTerm RTId = "1"

termBody :: ResourceTerm -> String
termBody RTId = ""
termBody t = showTerm t

-- | A template with known coefficients, e.g. @½·log(|t|) + log(|t|+1) + 1@.
showBound :: Map ResourceTerm Rational -> String
showBound m = joinSigned [(v, termBody t) | (t, v) <- M.toList m, v /= 0]

-- | Resource expressions whose coefficients may still be unknowns (potential
-- functions before a solution is applied).
showRScalarExpr :: FreeModule' -> String
showRScalarExpr m = case parts of
  [] -> "0"
  _ -> intercalate " + " parts
  where
    parts = [part s t | (t, s) <- M.toList m, not (isZeroScalar s)]
    part (RSConst k) t = joinSigned [(k, termBody t)]
    part s RTId = showScalar s
    part s t = showScalar s ++ "·" ++ showTerm t

type FreeModule' = Map ResourceTerm RScalar

isZeroScalar :: RScalar -> Bool
isZeroScalar (RSConst 0) = True
isZeroScalar _ = False

showScalar :: RScalar -> String
showScalar (RSConst k) = showRat k
showScalar (RSCoeff i t) = "Q" ++ show i ++ "[" ++ showTerm t ++ "]"
showScalar (RSAdd a b) = "(" ++ showScalar a ++ " + " ++ showScalar b ++ ")"
showScalar (RSMul a b) = showScalar a ++ "·" ++ showScalar b

showPattern :: Pattern a -> String
showPattern (PVar _ x) = T.unpack x
showPattern (PWildcard _) = "_"
showPattern (PConst _ c []) = T.unpack c
showPattern (PConst _ c args) = unwords (T.unpack c : map arg args)
  where arg p@(PConst _ _ (_ : _)) = "(" ++ showPattern p ++ ")"
        arg p = showPattern p

--------------------------------------------------------------------------------
-- Linear forms
--------------------------------------------------------------------------------

data Atom = ACoeff Coeff | AVar Int | AOne
  deriving (Eq, Ord)

type Linear = Map Atom Rational

linear :: ArithExpr -> Maybe Linear
linear (ConstTerm c) = Just (M.singleton AOne c)
linear (VarTerm v) = Just (M.singleton (AVar v) 1)
linear (CoeffTerm c) = Just (M.singleton (ACoeff c) 1)
linear (Sum es) = M.unionsWith (+) <$> mapM linear es
linear (Diff []) = Just M.empty
linear (Diff (e : es)) = do
  a <- linear e
  bs <- mapM linear es
  return $ M.unionWith (+) a (M.map negate (M.unionsWith (+) bs))
linear (Minus e) = M.map negate <$> linear e
linear (Prod es) = foldM mul (M.singleton AOne 1) =<< mapM linear es
  where
    mul a b
      | Just k <- constOnly a = Just (M.map (* k) b)
      | Just k <- constOnly b = Just (M.map (* k) a)
      | otherwise = Nothing

nonZero :: Linear -> Linear
nonZero = M.filter (/= 0)

constOnly :: Linear -> Maybe Rational
constOnly m = case M.toList (nonZero m) of
  [] -> Just 0
  [(AOne, k)] -> Just k
  _ -> Nothing

singleCoeff :: Linear -> Maybe Coeff
singleCoeff m = case M.toList (nonZero m) of
  [(ACoeff c, 1)] -> Just c
  _ -> Nothing

-- | Renders a linear form. Coefficients indexed by the row's own term are
-- abbreviated as @Q_i[·]@, and long runs of weakening variables are summarised.
showLinear :: Maybe ResourceTerm -> Linear -> String
showLinear t0 m = joinSigned (coeffs ++ vars ++ consts)
  where
    nz = nonZero m
    coeffs = [(k, coeffRef t0 c) | (ACoeff c, k) <- M.toList nz]
    varList = [(v, k) | (AVar v, k) <- M.toList nz]
    vars
      | length varList <= 3 = [(k, "k" ++ show v) | (v, k) <- varList]
      | otherwise = [(1, "Σ " ++ show (length varList) ++ " k")]
    consts = [(k, "") | Just k <- [M.lookup AOne nz]]

coeffRef :: Maybe ResourceTerm -> Coeff -> String
coeffRef t0 (Coeff i t)
  | Just t == t0 = "Q" ++ show i ++ "[·]"
  | otherwise = "Q" ++ show i ++ "[" ++ showTerm t ++ "]"

showArith :: ArithExpr -> String
showArith e = case linear e of
  Just l -> showLinear Nothing l
  Nothing -> case e of
    Prod es -> intercalate "·" (map paren es)
    Sum es -> intercalate " + " (map showArith es)
    Diff es -> intercalate " − " (map paren es)
    Minus x -> "−" ++ paren x
    _ -> "?"
  where paren x@(Sum _) = "(" ++ showArith x ++ ")"
        paren x@(Diff _) = "(" ++ showArith x ++ ")"
        paren x = showArith x

showFormula :: Formula -> String
showFormula (Eq a b) = showArith a ++ " = " ++ showArith b
showFormula (Le a b) = showArith a ++ " ≤ " ++ showArith b
showFormula (Ge a b) = showArith a ++ " ≥ " ++ showArith b
showFormula (Impl a b) = "(" ++ showFormula a ++ ") → (" ++ showFormula b ++ ")"
showFormula (Iff a b) = "(" ++ showFormula a ++ ") ↔ (" ++ showFormula b ++ ")"
showFormula (Not a) = "¬(" ++ showFormula a ++ ")"
showFormula (Or fs) = intercalate " ∨ " (map (\f -> "(" ++ showFormula f ++ ")") fs)
showFormula (And fs) = intercalate " ∧ " (map (\f -> "(" ++ showFormula f ++ ")") fs)
showFormula (Atom v) = "b" ++ show v
showFormula Bot = "⊥"

--------------------------------------------------------------------------------
-- Constraint rows
--------------------------------------------------------------------------------

data ConstraintRow = ConstraintRow
  { crTerm :: String
  , crLhs :: String
  , crOp :: String
  , crRhs :: String
  , crWeakNonNeg :: Bool -- ^ a @k ≥ 0@ side condition of a weakening
  }

constraintRow :: Formula -> ConstraintRow
constraintRow f = case f of
  Ge (VarTerm v) (ConstTerm 0) -> ConstraintRow "" ("k" ++ show v) "≥" "0" True
  Eq a b -> rel "=" a b
  Le a b -> rel "≤" a b
  Ge a b -> rel "≥" a b
  _ -> ConstraintRow "" (showFormula f) "" "" False
  where
    rel op a b = case (linear a, linear b) of
      (Just la, Just lb)
        | Just (Coeff i t) <- singleCoeff la ->
            ConstraintRow (showTerm t) ("Q" ++ show i) op (showLinear (Just t) lb) False
        | Just (Coeff i t) <- singleCoeff lb ->
            ConstraintRow (showTerm t) (showLinear (Just t) la) op ("Q" ++ show i) False
        | otherwise ->
            ConstraintRow "" (showLinear Nothing la) op (showLinear Nothing lb) False
      _ -> ConstraintRow "" (showArith a) op (showArith b) False

-- | Template ids mentioned by a formula.
coeffIds :: Formula -> S.Set Int
coeffIds f = case f of
  Eq a b -> ids a <> ids b
  Le a b -> ids a <> ids b
  Ge a b -> ids a <> ids b
  Impl a b -> coeffIds a <> coeffIds b
  Iff a b -> coeffIds a <> coeffIds b
  Not a -> coeffIds a
  Or fs -> S.unions (map coeffIds fs)
  And fs -> S.unions (map coeffIds fs)
  _ -> S.empty
  where
    ids (CoeffTerm (Coeff i _)) = S.singleton i
    ids (Sum es) = S.unions (map ids es)
    ids (Diff es) = S.unions (map ids es)
    ids (Prod es) = S.unions (map ids es)
    ids (Minus e) = ids e
    ids _ = S.empty

--------------------------------------------------------------------------------
-- Weakening
--------------------------------------------------------------------------------

-- | One Farkas multiplier of a weakening step, read back as the inequality
-- between resource terms it certifies.
data WeakeningVar = WeakeningVar
  { wvVar :: Int
  , wvSmaller :: String
  , wvLarger :: String
  , wvIsMono :: Bool -- ^ a plain comparison of two terms; otherwise an axiom instance
  }

-- | Reconstructs the columns of the weakening matrix from rows of the shape
-- @p[t] ≤ q[t] + Σ a_j·k_j@.
weakeningVars :: [Formula] -> [WeakeningVar]
weakeningVars cs = [classify v es | (v, es) <- M.toList cols]
  where
    rows = [ (t, lb)
           | Le a b <- cs
           , Just la <- [linear a]
           , Just (Coeff _ t) <- [singleCoeff la]
           , Just lb <- [linear b] ]
    cols = M.fromListWith (flip (++))
      [(v, [(t, k)]) | (t, lb) <- rows, (AVar v, k) <- M.toList lb, k /= 0]
    classify v es =
      let smaller = [(k, termBody t) | (t, k) <- sortOn fst es, k > 0]
          larger = [(negate k, termBody t) | (t, k) <- sortOn fst es, k < 0]
          mono = length es == 2 && all ((== 1) . abs . snd) es
      in WeakeningVar v (joinSigned smaller) (joinSigned larger) mono
