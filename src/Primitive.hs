{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module Primitive where

import Data.Text(Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Data.List (intercalate)

import Data.Ratio
import Debug.Trace hiding (traceShow)
import Data.Maybe

dbg :: String -> (a -> String) -> a -> a
dbg label f x = trace (label ++ ": " ++ f x) x

type Id = Text

enumId :: Int -> Id
enumId n = T.pack $ "?" ++ show n

type Substitution = Map Id Id

applySubst :: Substitution -> Id -> Id
applySubst s x = fromMaybe x (s M.!? x)

data IntWithInf = Inf | NotInf Int
  deriving Eq

infinity :: IntWithInf
infinity = Inf

instance Num IntWithInf where
  (+) Inf _ = Inf
  (+) _ Inf = Inf
  (+) (NotInf x) (NotInf y) = NotInf (x + y)
  (-) Inf _ = Inf
  (-) _ Inf = error "can not subtract integer from infinity"
  (-) (NotInf x) (NotInf y) = NotInf (x - y)
  (*) Inf _ = Inf
  (*) _ Inf = Inf
  (*) (NotInf x) (NotInf y) = NotInf (x * y)
  abs Inf = Inf
  abs (NotInf x) = NotInf (abs x)
  signum Inf = 1
  signum (NotInf x) = NotInf (signum x)
  fromInteger x = NotInf $ fromInteger x
  
instance Ord IntWithInf where
  (<=) Inf _ = False
  (<=) _ Inf = True
  (<=) (NotInf x) (NotInf y) = x <= y

toIntegerExact :: Rational -> Maybe Integer
toIntegerExact r
  | denominator r == 1 = Just (numerator r)
  | otherwise          = Nothing             

traceShow x = trace (show x) x

traceShowV msg x = trace (msg ++ ": " ++ show x) x

printTerms :: (Ord a, Num a) => (a -> String -> String) -> [(String, a)] -> String
printTerms combinator [] = "" 
printTerms combinator ((t,c):xs) | c == 0 = printTerms' xs
                                 | c > 0 =  combinator c t ++ printTerms' xs
                                 | c < 0 = " - " ++ combinator (abs c) t ++ printTerms' xs
  where printTerms' [] = ""
        printTerms' ((t,c):xs) | c == 0 = printTerms' xs
                               | c < 0 = " - " ++ combinator (abs c) t ++ printTerms' xs
                               | c > 0 = " + " ++ combinator c t ++ printTerms' xs

class PrettyPrint a where
  prettyPrint :: a -> String

instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrint = intercalate ", " . map prettyPrint

instance PrettyPrint Rational where
  prettyPrint r
    | denominator r == 1 = show (numerator r)
    | otherwise          = show (numerator r) ++ "/" ++ show (denominator r) where
  
class Substitutable a where
  subst :: M.Map Id Id -> a -> a

instance (Substitutable a) => Substitutable [a] where
  subst s = map (subst s)

instance (Ord a, Substitutable a) => Substitutable (Set a) where
  subst :: (Ord a, Substitutable a) => Map Id Id -> Set a -> Set a
  subst s = S.map (subst s)

instance Substitutable Id where
  subst env var = M.findWithDefault var var env

unionMap :: (Ord b) => (a -> Set b) -> [a] -> Set b
unionMap f xs = S.unions $ map f xs

class HasVars a where
  freeVars :: a -> Set Id

instance (HasVars a) => HasVars [a] where
  freeVars l = S.unions (map freeVars l)

instance (HasVars a) => HasVars (Set a) where
  freeVars l = S.unions (S.map freeVars l)  

substVar :: (Substitutable a) => Id -> Id -> a -> a
substVar x y = subst (M.singleton x y)

substVars :: (Substitutable a) => [Id] -> [Id] -> a -> a
substVars xs ys = subst (M.fromList (zip xs ys)) 

