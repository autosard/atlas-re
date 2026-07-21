{-# LANGUAGE TemplateHaskell #-}

module Syntax.ResourceExpression.Size where

import qualified Data.Map as M
import Data.Map (Map)
import Lens.Micro.Platform
import Data.List (intercalate)
import qualified Data.Text as T

import Primitive (Id, HasVars(..), Substitutable(..), PrettyPrint(..))

data SizeSum = SizeSum {
  _ssCoeffs :: Map Id Int,
  _ssConstant :: Int
  } deriving (Ord, Eq, Show)

makeLenses ''SizeSum

emptySizeSum = SizeSum M.empty 0

sizeConst = SizeSum M.empty
sizeVar x = SizeSum (M.singleton x 1) 0
sizeScalar x k = SizeSum (M.singleton x k) 0

add :: SizeSum -> SizeSum -> SizeSum
add s1 s2 = SizeSum 
  { _ssCoeffs = M.unionWith (+) (_ssCoeffs s1) (_ssCoeffs s2)
  , _ssConstant = (_ssConstant s1) + (_ssConstant s2)
  }

scale :: Int -> SizeSum -> SizeSum
scale k = (ssConstant %~ (* k))
          . (ssCoeffs %~ M.map (* k))

sizeSubst :: (Id, SizeSum) -> SizeSum -> SizeSum
sizeSubst (x, v) sum
  | (M.member x (sum^.ssCoeffs)) =
      let k = (sum^.ssCoeffs) M.! x
          sum' = sum & ssCoeffs %~ M.delete x in
        add (scale k v) sum'
  | otherwise = sum
  

data SizeTerm = VarTerm Id Int | ConstTerm Int

addSizeTerm :: SizeTerm -> SizeSum -> SizeSum
addSizeTerm (VarTerm x k) = ssCoeffs %~ M.insertWith (+) x k
addSizeTerm (ConstTerm k) = ssConstant %~ (+ k)

sizeFromList :: [SizeTerm] -> SizeSum
sizeFromList = foldr addSizeTerm emptySizeSum

instance Substitutable SizeSum where
  subst env (SizeSum cs c) = SizeSum
    { _ssCoeffs = M.mapKeysWith (+) (subst env) cs
    , _ssConstant = c
    }

instance HasVars SizeSum where
  freeVars sum = M.keysSet (_ssCoeffs sum)


instance PrettyPrint SizeSum where
  prettyPrint (SizeSum cs k)
    | null terms && k == 0 = "0"
    | otherwise            = intercalate " + " terms
    where
      -- Formats a single (var, coefficient) pair
      prettyCoeff var 1 = var
      prettyCoeff var c = show c ++ "*" ++ var
  
      varTerms  = [ prettyCoeff (T.unpack v) c | (v, c) <- M.toList cs, c /= 0 ]
      constTerm = [ show k | k /= 0 ]
      
      terms = varTerms ++ constTerm
