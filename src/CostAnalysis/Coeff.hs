{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module CostAnalysis.Coeff where

import Data.Text(Text)
import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe (mapMaybe)

import Primitive(Id, Substitution, applySubst)

data Factor = Const Int | Arg Id [Int]
  deriving (Eq, Ord)

var :: Factor -> Maybe Id
var (Const _) = Nothing
var (Arg x _) = Just x

data CoeffIdx = Pure Id | Mixed (Set Factor)
  deriving (Eq, Ord)

class Index a where
  toIdx :: a -> CoeffIdx

instance Index Id where
  toIdx = Pure

instance Index CoeffIdx where
  toIdx = id
    
instance Index [Factor] where
  toIdx = mixed . S.fromList

instance Index (Set Factor) where
  toIdx = mixed

data Coeff =
  Coeff
    Int -- ^ Unique identifier for the annotation; used together with coefficent index to identify coeffients when encoding them for smt. 
    Text -- ^ Human readable label, e.g. \"Q\", \"P\", ...
    Text -- ^ Human readable comment, to trace the origin of the coefficient, e.g. "log".
    CoeffIdx -- ^ An index to identify the coefficient.
  deriving (Eq, Ord, Show)


isPure :: CoeffIdx -> Bool
isPure (Pure _) = True
isPure _ = False

getIdx :: Coeff -> CoeffIdx
getIdx (Coeff _ _ _ idx) = idx

printCoeff :: Coeff -> String
printCoeff (Coeff id label comment idx) = "q" ++ show id ++ "[" ++ T.unpack label ++ "]" ++ show idx


instance Show Factor where
  show (Const c) = show c
  show (Arg x a) = T.unpack x ++ "^" ++ show a

infixl 9 ^
(^) :: Id -> Int -> Factor
(^) x a = Arg x [a]

factorNotZero :: Factor -> Bool
factorNotZero (Arg _ a) = not $ all (==0) a
factorNotZero (Const c) = c /= 0



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

coeffArgs :: CoeffIdx -> [Id]
coeffArgs (Pure x) = [x]
coeffArgs idx = foldr go [] . S.toList . idxToSet $ idx
  where go (Const _) xs = xs
        go (Arg x _) xs = x:xs

getArg (Arg _ a) = Just a
getArg (Const _) = Nothing

getArgs (Mixed facs) = mapMaybe getArg $ S.toList facs
getArgs _ = error "cannot extract factor for pure index."

facForVar' :: CoeffIdx -> Id -> Maybe [Int]
facForVar' (Mixed idx) x = getArg =<< L.find (matchesVar x) (S.toList idx)
facForVar' _ _ = error "cannot extract factor for pure index."

facForVar :: CoeffIdx -> Id -> Int
facForVar idx x = case facForVar' idx x of
  Just [a] -> a
  Nothing -> 0

facForVar2 :: CoeffIdx -> Id -> (Int, Int)
facForVar2 idx x = case facForVar' idx x of
  Just [x1, x2] -> (x1, x2)
  Nothing -> (0, 0)

facForVar3 :: CoeffIdx -> Id -> (Int, Int, Int)
facForVar3 idx x =
  case facForVar' idx x of
    Just [x1, x2, x3] -> (x1, x2, x3)
    Nothing -> (0, 0, 0)

varsForFac :: CoeffIdx -> [Int] -> [Id]
varsForFac (Mixed facs) fac = foldr go [] facs
  where go (Arg x f) a | f == fac = x:a
        go (Arg x f) a = a
        go (Const _) a = a

onlyFacsOfLen :: Int -> CoeffIdx -> Bool
onlyFacsOfLen n idx@(Mixed _) = all (\xs -> length xs == n) . getArgs $ idx
onlyFacsOfLen _ _ = False

onlyFac :: [Int] -> CoeffIdx -> Bool
onlyFac f = all (== f) . getArgs

restrictFacs :: CoeffIdx -> [Int] -> Set Factor
restrictFacs (Mixed facs) a = S.filter go facs
  where go fac = case getArg fac of
          Just b -> a == b
          Nothing -> True
restrictFacs  _ _ = error "pure index"

restrictFacsNoConst :: CoeffIdx -> [Int] -> Set Factor
restrictFacsNoConst (Mixed facs) a = S.filter go facs
  where go fac = case getArg fac of
          Just b -> a == b
          Nothing -> False
restrictFacsNoConst  _ _ = error "pure index"

-- without const
except :: CoeffIdx -> [Id] -> Set Factor
except (Mixed idx) xs = S.filter (\f -> not (any (`matchesVar` f) xs)) idx

-- with const
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

intersect :: CoeffIdx -> [Id] -> [Id]
intersect (Mixed idx) xs = let s = mapMaybe var (S.toList idx) in
  xs `L.intersect` s

onlyVars :: CoeffIdx -> [Id] -> Bool
onlyVars idx xs = null $ except idx xs

onlyVarsOrConst :: CoeffIdx -> [Id] -> Bool
onlyVarsOrConst idx xs = null $ varsExcept idx xs

singleVar :: CoeffIdx -> Bool
singleVar (Pure _) = True
singleVar idx = length (coeffArgs idx) == 1

hasArgs :: [Id] -> CoeffIdx -> Bool
hasArgs xs (Pure x) = x `elem` xs
hasArgs xs idx = onlyVars idx xs

containsArgs :: [Id] -> CoeffIdx -> Bool
containsArgs xs (Pure x) = x `elem` xs
containsArgs xs idx = not . null $ intersect idx xs 

hasArgsOrConst :: [Id] -> CoeffIdx -> Bool
hasArgsOrConst xs (Pure x) = x `elem` xs
hasArgsOrConst xs idx = onlyVarsOrConst idx xs 

justConst :: CoeffIdx -> Bool
justConst (Mixed idx) = all isConst idx
justConst _ = False

justVars :: CoeffIdx -> Bool
justVars (Mixed idx) = not $ any isConst idx
justVars _ = False

idxNull :: CoeffIdx -> Bool
idxNull (Mixed s) = null s
idxNull _ = False

idxSum :: CoeffIdx -> Int
idxSum (Mixed idx) = foldr go 0 idx
  where go (Const c) s = s + c
        go (Arg _ a) s = s + sum a
idxSum _ = error "idx sum only makes sense for mixed indicies."

idxSumVar :: CoeffIdx -> Int
idxSumVar (Mixed idx) = foldr go 0 idx
  where go (Const c) s = 0
        go (Arg _ a) s = s + sum a
idxSumVar _ = error "idx sum only makes sense for mixed indicies."        

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
substitute from to idx@(Pure x) = case L.elemIndex x from of
  Just i -> Pure $ to !! i
  Nothing -> error $ "invalid index " ++ show idx ++ show from
substitute from to idx@(Mixed factors) = Mixed (S.map subFactor factors)
  where subFactor (Const c) = Const c
        subFactor (Arg x a) = case L.elemIndex x from of
          Just i -> Arg (to !! i) a
          Nothing -> error $ "invalid index" ++ show idx ++ "[" ++ show from ++ " -> " ++ show to ++ "]"


substitute' :: Substitution -> CoeffIdx -> CoeffIdx
substitute' s (Pure x) = Pure $ applySubst s x
substitute' s (Mixed factors) = Mixed (S.map subFactor factors)
  where subFactor (Const c) = Const c
        subFactor (Arg x a) = Arg (applySubst s x) a


stubArgVars :: [Id] -> Int -> [Id]
stubArgVars args l = args ++ replicate (l - length args) "!"

class HasCoeffs a where
  getCoeffs :: a -> [Coeff]

instance HasCoeffs a => HasCoeffs [a] where
  getCoeffs = concatMap getCoeffs

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
