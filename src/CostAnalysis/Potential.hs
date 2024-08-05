{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}

module CostAnalysis.Potential where

import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.List as L
import Prelude hiding ((!))
import qualified Data.Vector as V
import Data.Set(Set)
import qualified Data.Set as S
import Lens.Micro.Platform


import Primitive(Id)
import CostAnalysis.Rules ( WeakenArg )
import CostAnalysis.Coeff
import CostAnalysis.Constraint
import CostAnalysis.Optimization (OptiMonad, Target)
import CostAnalysis.RsrcAnn
import Typing.Type ( Type )


type ExpertKnowledge = (V.Vector (V.Vector Int), [Int])

data AnnRanges = AnnRanges {
  rangeA :: ![Int],
  rangeB :: ![Int],
  rangeBNeg :: ![Int]}

data Potential = Potential {
  -- Supported types
  types :: [Type],
  ranges :: AnnRanges,
  
  -- Annotation manipulation
  
  -- | @ 'rsrcAnn' id label comment vars (rangeA, rangeB) pure@ constructs a fresh resource annotation with arguments from @vars@ (types are considered). @rangeA@, @rangeB@ are used to define non-zero coefficients. When @pure@ is True, pure coeffients for the arguments are generated. @id@ specifies a unique identifier for the annotation and @label@ is the human readable label, e.g \"Q\", \"Q\'\" or \"P\".
  rsrcAnn :: Int -> Text -> Text -> [(Id, Type)] -> ([Int], [Int]) -> Bool -> RsrcAnn, 

  -- | @ 'constCoeff'@ returns the coefficient index for the constant basic potential function.
  constCoeff :: CoeffIdx,
  
  
  -- Constraint generation
  
  -- | @ 'cConst' q q'@ returns constraints that guarantee \[\phi(\Gamma \mid Q) = \phi(\Delta \mid Q') \text{ where } |\Gamma| = |Q|, |\Delta| = |Q'|\]  
  cConst :: RsrcAnn -> RsrcAnn -> [Constraint],
  -- | @ 'cMatch' q p_ x ys = (p, cs)@ defines @p@ with the empty annotation @p_@ from @q@ by constraints @cs@, guaranteeing \[\phi(\Gamma, x \mid Q) = \phi(\Gamma, \vec{y} \mid P)\] where @x@ is the variable that matched and @ys@ is the pattern variables.
  cMatch :: RsrcAnn -> RsrcAnn -> Id -> [(Id, Type)] -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetBinding' q p_ = (p, cs)@
  cLetBindingBase :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),

   -- | @ 'cLetBinding' q p_ = (p, cs)@
  cLetBinding :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),
  
  -- | @ 'cLetBodyBase' q r_ p' = (r, cs)@
  cLetBodyBase :: RsrcAnn -> RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetBody' q r_ p p' ps' x bdes = (r, cs)@
  cLetBody :: RsrcAnn -> RsrcAnn -> RsrcAnn -> RsrcAnn -> AnnArray -> Id -> [Set Factor] -> (RsrcAnn, [Constraint]),

  -- | @ 'cLetCf' q ps_ ps'_ x bdes = (ps, ps', cs)@
  cLetCf :: RsrcAnn -> AnnArray -> AnnArray -> Id -> ([Id], [Id]) ->[Set Factor] -> (AnnArray, AnnArray, [Constraint]),
  
  -- | @ 'cLet' q p p' ps ps' r x@
  cLet :: Bool -> RsrcAnn -> RsrcAnn -> RsrcAnn
    -> AnnArray -> AnnArray -> RsrcAnn -> Id -> [Constraint],
    
  -- | @ 'cWeakenVar' q r @
  cWeakenVar :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint]),
  
  genExpertKnowledge :: Set WeakenArg -> RsrcAnn -> RsrcAnn -> ExpertKnowledge,
  
  -- | @ 'cOptimize' q q' @ returns constraints that minimize \[\Phi(\Gamma\mid Q) - \Phi(\Gamma\mid Q')\]
  cOptimize :: RsrcAnn -> RsrcAnn -> OptiMonad Target,
  
  printBasePot :: Coeff -> Rational -> String}

defaultNegAnn :: Potential -> Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn
defaultNegAnn pot id label comment args = rsrcAnn pot id label comment args abRanges True
  where abRanges = (rangeA (ranges pot), rangeBNeg (ranges pot))
  
defaultAnn :: Potential -> Int -> Text -> Text -> [(Id, Type)] -> RsrcAnn
defaultAnn pot id label comment args = rsrcAnn pot id label comment args abRanges True
  where abRanges = (rangeA (ranges pot), rangeB (ranges pot))

eqExceptConst :: Potential -> RsrcAnn -> RsrcAnn -> [Constraint]
eqExceptConst pot q p = [Eq (q!?idx) (p!?idx)
                        | idx <- S.toList $ (p^.coeffs) `S.union` (p^.coeffs),
                          idx /= constCoeff pot]

-- | @ 'cPlusConst' q p c@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) + c\] where @c@ is constant.
cPlusConst :: Potential -> RsrcAnn -> RsrcAnn -> Rational -> [Constraint]
cPlusConst pot q p c = let qs = q^.args in
  Eq (q!constIdx) (Sum [p!constIdx, ConstTerm c]) :
  eqExceptConst pot q p
  where constIdx = constCoeff pot

-- | @ 'cMinusVar' q p@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(*\mid P) - k\] where @k@ is a fresh variable.
cMinusVar :: Potential -> RsrcAnn -> RsrcAnn -> Term -> [Constraint]
cMinusVar pot q p k = let qs = q^.args in 
  Eq (q!constIdx) (Sum [p!constIdx, k]) :
  eqExceptConst pot q p
  where constIdx = constCoeff pot


  -- | @ 'forAllCombinations' q xs (rangeA, rangeB) x@ generates an index for all combinations of variables in @xs@ and the variable @x@, based on the indices in @q@.
forAllCombinations :: RsrcAnn -> [Id] -> ([Int], [Int]) -> Id -> [Set Factor] 
forAllCombinations q xs (rangeA, rangeB) x =
  [S.unions [xsIdx, S.singleton xIdx, S.singleton cIdx]
  | idx <- mixes q,
    let xsIdx = varsExcept idx xs,
    d <- rangeA,
    d /= 0,
    let xIdx = Arg x d,
    cIdx <- map Const rangeB] 


--  -- | @ 'cPlusMulti' q p r k@ returns constraints that guarantee \[\phi(*\mid Q) = \phi(* \mid P) + \phi(*\mid R) \cdot K\].
-- cPlusMulti :: RsrcAnn -> RsrcAnn -> RsrcAnn -> Var -> [Constraint],
-- cPlusMulti q p r k = q `annEq` (annAdd p (annScalarMul r k))

calculateBound :: (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> Map Coeff Rational
calculateBound (from, to) solution = M.fromList $ map subtract (getCoeffs from)
  where [arg] = annVars to
        subtract left@(Coeff _ _ _ idx) = let
          (CoeffTerm right) = to!substitute idx arg in
          case solution M.!? right of
            Just rightValue -> case solution M.!? left of
              Just leftValue -> let diff =  leftValue - rightValue in (left, diff)
                --if diff >= 0 then (left, diff) else error "Negative coefficient in result bound."
              Nothing -> error $ "No such base term on the left hand side for '" ++ show right ++ "'."
            Nothing -> case solution M.!? left of
              Just leftValue -> (left, leftValue)
              Nothing -> (left, 0)
            

printBound :: Potential -> (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> String
printBound pot sig solution = if L.null terms then "0" else
  L.intercalate " + " $ map (uncurry (printBasePot pot)) terms
  where terms = M.toList $ M.filter (0 /=) solution'
        solution' = calculateBound sig solution
  
