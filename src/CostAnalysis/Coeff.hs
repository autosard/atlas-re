{-# LANGUAGE StrictData #-}

module CostAnalysis.Coeff where

import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.List as L

import Primitive(Id)
import Data.Maybe (isJust)

data Coeff =
  Coeff
    Int -- ^ Unique identifier for the annotation; used together with coefficent index to identify coeffients when encoding them for smt. 
    Text -- ^ Human readable label, e.g. \"Q\", \"P\", ...
    Text -- ^ Human readable comment, to trace the origin of the coefficient, e.g. "log".
    CoeffIdx -- ^ An index to identify the coefficient.
  deriving (Eq, Ord, Show)

printCoeff :: Coeff -> String
printCoeff (Coeff id label comment idx) = "q" ++ show id ++ show idx

data Factor = Const Int | Arg Id Int
  deriving (Eq, Ord)

instance Show Factor where
  show (Const c) = show c
  show (Arg x a) = T.unpack x ++ "^" ++ show a

infixl 9 ^
(^) :: Id -> Int -> Factor
(^) = Arg


data CoeffIdx = Pure Id | Mixed (Set Factor)
  deriving (Eq, Ord)

-- for use in quasi quoter, to avoid "Illegal variable name"
mixed_ = Mixed

isConst (Const x) = True
isConst _ = False

constFactor :: CoeffIdx -> Int
constFactor (Mixed idx) = getConst $ L.find isConst (S.toList idx)
  where getConst (Just (Const x)) = x
        getConst Nothing = 0
constFactor _ = error "cannot extract const for pure index."

matchesVar x (Arg id _) = id == x
matchesVar _ _ = False

facForVar :: CoeffIdx -> Id -> Int
facForVar (Mixed idx) x = getArg $ L.find (matchesVar x) (S.toList idx)
  where getArg (Just (Arg _ a)) = a
        getArg Nothing = 0
facForVar _ _ = error "cannot extract const for pure index."

varsExcept :: CoeffIdx -> [Id] -> Set Factor
varsExcept (Mixed idx) xs = S.filter (\f -> not (any (`matchesVar` f) xs || isConst f)) idx
varsExcept _ _ = error "pure index"

onlyVars :: CoeffIdx -> Set Id -> Bool
onlyVars (Mixed idx) xs = null . S.filter isJust . S.map go $ idx
  where go (Arg id _) = if S.member id xs then Nothing else Just id
        go (Const _) = Nothing
onlyVars _ _ = error "pure index"

justConst (Mixed idx) = all isConst idx
justConst _ = error "pure index"

idxSum :: CoeffIdx -> Int
idxSum (Mixed idx) = foldr go 0 idx
  where go (Const c) s = s + c
        go (Arg _ a) s = s + a
idxSum _ = error "idx sum only makes sense for mixed indicies."

instance Show CoeffIdx where
  show (Pure x) = "(" ++ T.unpack x ++ ")"
  show (Mixed xs) = "(" ++ L.intercalate "," (map show (S.toDescList xs)) ++ ")"

substitute :: CoeffIdx -> Id -> CoeffIdx
substitute (Pure x) y = Pure y
substitute (Mixed factors) y = Mixed (S.map (subFactor y) factors)
  where subFactor _ (Const c) = Const c 
        subFactor y (Arg x a) = Arg y a



class HasCoeffs a where
  getCoeffs :: a -> [Coeff]

instance HasCoeffs a => HasCoeffs [a] where
  getCoeffs = concatMap getCoeffs
