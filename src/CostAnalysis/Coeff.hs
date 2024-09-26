{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}

module CostAnalysis.Coeff where

import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.List as L

import Primitive(Id)

data Coeff =
  Coeff
    Int -- ^ Unique identifier for the annotation; used together with coefficent index to identify coeffients when encoding them for smt. 
    Text -- ^ Human readable label, e.g. \"Q\", \"P\", ...
    Text -- ^ Human readable comment, to trace the origin of the coefficient, e.g. "log".
    CoeffIdx -- ^ An index to identify the coefficient.
  deriving (Eq, Ord, Show)

getIdx :: Coeff -> CoeffIdx
getIdx (Coeff _ _ _ idx) = idx

printCoeff :: Coeff -> String
printCoeff (Coeff id label comment idx) = "q" ++ show id ++ "[" ++ T.unpack label ++ "]" ++ show idx

data Factor = Const Int | Arg Id Int
  deriving (Eq, Ord)

instance Show Factor where
  show (Const c) = show c
  show (Arg x a) = T.unpack x ++ "^" ++ show a

infixl 9 ^
(^) :: Id -> Int -> Factor
(^) = Arg

factorNotZero :: Factor -> Bool
factorNotZero (Arg _ a) = a /= 0
factorNotZero (Const c) = c /= 0


data CoeffIdx = Pure Id | Mixed (Set Factor)
  deriving (Eq, Ord)

mixed :: Set Factor -> CoeffIdx
mixed facs = Mixed (S.filter factorNotZero facs)

idxToSet :: CoeffIdx -> Set Factor
idxToSet (Mixed idx) = idx
idxToSet _ = error "pure index"

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
facForVar _ _ = error "cannot extract factor for pure index."

-- with const
except :: CoeffIdx -> [Id] -> Set Factor
except (Mixed idx) xs = S.filter (\f -> not (any (`matchesVar` f) xs)) idx

-- without const
varsExcept :: CoeffIdx -> [Id] -> Set Factor
varsExcept (Mixed idx) xs = S.filter (\f -> not (any (`matchesVar` f) xs || isConst f)) idx
varsExcept _ _ = error "pure index"

-- with const
restrict :: CoeffIdx -> [Id] -> Set Factor
restrict (Mixed idx) xs = S.filter go idx
  where go (Arg id _) = S.member id (S.fromList xs)
        go (Const _) = True
restrict _ _ = error "pure index"

-- without const
varsRestrict :: CoeffIdx -> [Id] -> Set Factor
varsRestrict (Mixed idx) xs = S.filter go idx
  where go (Arg id _) = S.member id (S.fromList xs)
        go (Const _) = False
varsRestrict _ _ = error "pure index"

onlyVars :: CoeffIdx -> [Id] -> Bool
onlyVars idx xs = null $ except idx xs

onlyVarsOrConst :: CoeffIdx -> [Id] -> Bool
onlyVarsOrConst idx xs = null $ varsExcept idx xs 

justConst :: CoeffIdx -> Bool
justConst (Mixed idx) = all isConst idx
justConst _ = error "pure index"

idxSum :: CoeffIdx -> Int
idxSum (Mixed idx) = foldr go 0 idx
  where go (Const c) s = s + c
        go (Arg _ a) s = s + a
idxSum _ = error "idx sum only makes sense for mixed indicies."

facToTuple (Arg x a) = (x,a)
facToTuple (Const a) = (":c",a)
tupleToFac :: (Id, Int) -> Factor
tupleToFac (":c", a) = Const a
tupleToFac (x, a) = Arg x a

idxToMap :: CoeffIdx -> Map Id Int
idxToMap = M.fromList . S.toList . S.map facToTuple . idxToSet

idxFromMap :: Map Id Int -> CoeffIdx
idxFromMap = mixed . S.fromList . map tupleToFac . M.toList

addIdxs :: CoeffIdx -> CoeffIdx -> CoeffIdx
addIdxs idxX idxY = idxFromMap $ M.unionWith (+) (idxToMap idxX) (idxToMap idxY)

instance Show CoeffIdx where
  show :: CoeffIdx -> String
  show (Pure x) = "(" ++ T.unpack x ++ ")"
  show (Mixed xs) = "(" ++ L.intercalate "," (map show (S.toDescList xs)) ++ ")"

substitute :: [Id] -> [Id] -> CoeffIdx -> CoeffIdx
substitute from to (Pure x) = case L.elemIndex x from of
  Just i -> Pure $ to !! i
  Nothing -> error "invalid index"
substitute from to (Mixed factors) = Mixed (S.map subFactor factors)
  where subFactor (Const c) = Const c
        subFactor (Arg x a) = case L.elemIndex x from of
          Just i -> Arg (to !! i) a
          Nothing -> error "invalid index"


class HasCoeffs a where
  getCoeffs :: a -> [Coeff]

instance HasCoeffs a => HasCoeffs [a] where
  getCoeffs = concatMap getCoeffs
