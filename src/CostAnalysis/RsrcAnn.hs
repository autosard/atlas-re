{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module CostAnalysis.RsrcAnn where

import Prelude hiding (sum)

import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Data.Text(Text)
import Lens.Micro.Platform
import Data.Maybe (fromMaybe)


import Primitive(Id)
import CostAnalysis.Coeff
import Typing.Type
import Control.Monad.State
import CostAnalysis.Constraint


data RsrcAnn = RsrcAnn {
  _annId :: Int,
  _args :: [(Id, Type)],
  _label :: Text, -- ^ Human readable label, e.g. \"Q\", \"P\", ...
  _comment ::  Text, -- ^ Human readable comment, to trace the origin of the coefficient, e.g. "log".
  _coeffs :: Set CoeffIdx -- ^ non zero coefficients
  }
  deriving (Eq, Show)

makeLenses ''RsrcAnn

fromAnn :: Int -> Text -> Text -> RsrcAnn -> RsrcAnn
fromAnn id label comment ann = RsrcAnn id (ann^.args) label comment (ann^.coeffs)

isPure :: CoeffIdx -> Bool
isPure (Pure _) = True
isPure _ = False

mixes :: RsrcAnn -> [CoeffIdx]
mixes ann = S.toList . S.filter (not . isPure) $ ann^.coeffs

varsRestrictMixes :: RsrcAnn -> [Id] -> [CoeffIdx]
varsRestrictMixes ann xs = S.toList $ S.map (mixed . (`varsRestrict` xs)) . S.filter (not . isPure) $ ann^.coeffs

pures :: RsrcAnn -> [CoeffIdx]
pures ann = S.toList . S.filter isPure $ ann^.coeffs

constRange :: RsrcAnn -> [Int]
constRange q = S.toList $ foldr go S.empty (q^.coeffs) 
  where go (Pure _) consts = consts
        go coeff@(Mixed _) consts = S.insert (constFactor coeff) consts

annVars :: RsrcAnn -> [Id]
annVars = map fst . _args

class AnnLike a where
  infixl 9 !
  (!) :: (Index i, Show i) => a -> i -> Term
  infixl 9 !?
  (!?) :: (Index i, Show i) => a -> i -> Term
  definedIdxs :: a -> Set CoeffIdx
  argVars :: a -> [Id]

instance AnnLike RsrcAnn where
  argVars = annVars
  definedIdxs q = q^.coeffs
  (!) ann idx = case coeffForIdx ann (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> error $ "Invalid index '" ++ show idx ++ "' for annotation '" ++ show ann ++ "'."
  (!?) ann idx = case coeffForIdx ann (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> ConstTerm 0


class Index a where
  toIdx :: a -> CoeffIdx

coeffFromAnn :: RsrcAnn -> CoeffIdx -> Coeff
coeffFromAnn ann = Coeff (ann^.annId) (ann^.label) (ann^.comment)

coeffForIdx :: RsrcAnn -> CoeffIdx -> Maybe Coeff
coeffForIdx ann idx =
  if S.member idx (definedIdxs ann) then
    Just $ coeffFromAnn ann idx
  else Nothing

instance Index Id where
  toIdx = Pure

instance Index CoeffIdx where
  toIdx = id
    
instance Index [Factor] where
  toIdx = mixed . S.fromList

instance Index (Set Factor) where
  toIdx factors = mixed factors

data PointWiseOp = PointWiseOp {
  opArgs :: [Id] ,
  opCoeffs :: Map CoeffIdx Term}

instance AnnLike PointWiseOp where
  argVars = opArgs
  definedIdxs op =  M.keysSet $ opCoeffs op
  (!) op idx = opCoeffs op M.! toIdx idx
  (!?) op idx = fromMaybe (ConstTerm 0) $ opCoeffs op M.!? toIdx idx

annScalarMul :: RsrcAnn -> Term -> PointWiseOp
annScalarMul q k = PointWiseOp (annVars q) $
  M.fromList [(idx, prod [q!idx, k]) | idx <- S.toList (q^.coeffs)]

annAdd :: RsrcAnn -> PointWiseOp -> PointWiseOp
annAdd q op | annVars q == opArgs op = PointWiseOp (annVars q) $
  M.fromList [(idx, sum [q!?idx, op!?idx])
             | idx <- S.toList $ (q^.coeffs) `S.union` definedIdxs op]
            | otherwise = error "point wise operation not valid for annotation likes with different arguments."

annLikeAdd :: (AnnLike a, AnnLike b) => a -> b -> PointWiseOp
annLikeAdd q p | argVars q == argVars p = PointWiseOp (argVars q) $
             M.fromList [(idx, sum [q!?idx, p!?idx])
                        | idx <- S.toList $ definedIdxs q `S.union` definedIdxs p]
               | otherwise = error "point wise operation not valid for annotation likes with different arguments."


annLikeEq :: (AnnLike a, AnnLike b) => a -> b -> [Constraint]
annLikeEq q op = concat [eq (q!?idx) (op!?idx)
             | idx <- S.toList $ definedIdxs q `S.union` definedIdxs op]

annLikeUnify :: (AnnLike a, AnnLike b) => a -> b -> [Constraint]
annLikeUnify q p = concat [eq (q!?idx) (p!?substitute (argVars q) (argVars p) idx)
                          | idx <- S.toList $ definedIdxs q]

annEq :: RsrcAnn -> RsrcAnn -> [Constraint]
annEq q p | (length . _args $ q) /= (length . _args $ p) = error "Annotations with different lengths can not be equal."
          | otherwise = annLikeEq q p

type AnnArray = Map CoeffIdx RsrcAnn

elems :: AnnArray -> [RsrcAnn]
elems = M.elems

infixl 9 !!
(!!) :: AnnArray -> CoeffIdx -> RsrcAnn
(!!) arr k = case M.lookup k arr of
  Just c -> c
  Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation array."

data FunRsrcAnn = FunRsrcAnn {
  withCost :: (RsrcAnn, RsrcAnn),
  withoutCost :: (RsrcAnn, RsrcAnn)}
  deriving(Show)

type RsrcSignature = Map Id FunRsrcAnn

type CoeffDef s a = State s a

def :: Index i => i -> CoeffDef RsrcAnn Term
def i = do
  let idx = toIdx i
  coeffs %= (idx `S.insert`)
  ann <- get
  return $ ann!idx

defEntry :: CoeffIdx -> CoeffIdx -> CoeffDef AnnArray Term
defEntry arrIdx coeffIdx = do
  ix arrIdx . coeffs %= (coeffIdx `S.insert`)
  arr <- get
  return $ (arr M.! arrIdx)!coeffIdx

extendAnn :: RsrcAnn -> [CoeffDef RsrcAnn [Constraint]] -> (RsrcAnn, [Constraint])
extendAnn ann defs = (ann', concat cs)
  where (cs, ann') = runState def ann
        def = sequence defs
        
extendAnns :: AnnArray -> [CoeffDef AnnArray [Constraint]] -> (AnnArray, [Constraint])
extendAnns arr defs = (arr', concat cs)
  where (cs, arr') = runState def arr
        def = sequence defs

annLe :: RsrcAnn -> Map CoeffIdx Rational -> [Constraint]
annLe ann values = concat [le (ann!idx) $ ConstTerm (M.findWithDefault 0 idx values)
                          | idx <- S.toList $ definedIdxs ann]

-- annConstEq :: RsrcAnn -> Map CoeffIdx Rational -> [Constraint]
-- annConstEq ann values = concat [eq (ann!idx) $ ConstTerm (M.findWithDefault 0 idx values)
--                                | idx <- S.toList $ definedIdxs ann]

annLikeConstEq :: AnnLike a => a -> Map CoeffIdx Rational -> [Constraint]
annLikeConstEq ann values = concat [eq (ann!idx) $ ConstTerm (M.findWithDefault 0 idx values)
                                   | idx <- S.toList $ definedIdxs ann]
                        
instance HasCoeffs RsrcAnn where
  getCoeffs ann = map (coeffFromAnn ann) $ S.toList (ann^.coeffs)

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
  
instance HasCoeffs FunRsrcAnn where
  getCoeffs ann = (getCoeffs . withCost) ann ++ (getCoeffs . withoutCost) ann

instance HasCoeffs RsrcSignature where
  getCoeffs = concatMap getCoeffs . M.elems

-- printSolution :: (RsrcAnn, RsrcAnn) -> Map Coeff Rational -> String
-- printSolution (q, q') solution =
--   where printCoeffs p =
--         printCoeff :: Text -> CoeffIdx -> Rational
