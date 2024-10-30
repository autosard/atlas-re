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

data Factor = Const Int | Arg Id [Int]
  deriving (Eq, Ord)

instance Show Factor where
  show (Const c) = show c
  show (Arg x a) = T.unpack x ++ "^" ++ show a

infixl 9 ^
(^) :: Id -> Int -> Factor
(^) x a = Arg x [a]

factorNotZero :: Factor -> Bool
factorNotZero (Arg _ a) = not $ all (==0) a
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

facForVar' :: CoeffIdx -> Id -> [Int]
facForVar' (Mixed idx) x = getArg $ L.find (matchesVar x) (S.toList idx)
  where getArg (Just (Arg _ a)) = a
        getArg Nothing = []
facForVar' _ _ = error "cannot extract factor for pure index."

facForVar :: CoeffIdx -> Id -> Int
facForVar idx x = case facForVar' idx x of
  [a] -> a
  [] -> 0

facForVar2 :: CoeffIdx -> Id -> (Int, Int)
facForVar2 idx x = case facForVar' idx x of
  [x1, x2] -> (x1, x2)
  [] -> (0, 0)

facForVar3 :: CoeffIdx -> Id -> (Int, Int, Int)
facForVar3 idx x =
  case facForVar' idx x of
    [] -> (0, 0, 0)
    [x1, x2, x3] -> (x1, x2, x3)

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
justConst _ = False

idxSum :: CoeffIdx -> Int
idxSum (Mixed idx) = foldr go 0 idx
  where go (Const c) s = s + c
        go (Arg _ a) s = s + sum a
idxSum _ = error "idx sum only makes sense for mixed indicies."

facToTuple :: Factor -> (Id, [Int])
facToTuple (Arg x a) = (x,a)

tupleToFac :: (Id, [Int]) -> Factor
tupleToFac (x, a) = Arg x a

type OrderedCoeffIdx = (Map Id [Int], Int)

orderedIdx :: CoeffIdx -> OrderedCoeffIdx
orderedIdx idx = let as = M.fromList .
                       S.toList .
                       S.map facToTuple .
                       S.filter (not . isConst) $
                       idxToSet idx
                     c = constFactor idx in
                   (as, c)

fromOrderedIdx :: OrderedCoeffIdx -> CoeffIdx
fromOrderedIdx (as, c) = let as' = S.fromList . map tupleToFac . M.toList $ as
                             c' = Const c in
                           mixed $ S.insert c' as'

addIdxs :: CoeffIdx -> CoeffIdx -> CoeffIdx
addIdxs idxX idxY = let (xs, cx) = orderedIdx idxX
                        (ys, cy) = orderedIdx idxY
                        as = M.unionWith (zipWith (+)) xs ys
                        c = cx + cy in
                      fromOrderedIdx (as, c)

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
