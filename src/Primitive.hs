module Primitive where

import Data.Text(Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as M
import Data.Ratio
import Debug.Trace hiding (traceShow)
import Data.Maybe

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

printRat :: Rational -> String
printRat r = let n = numerator r
                 d = denominator r in
               case d of
                 1 -> show n
                 _ -> show n ++ "/" ++ show d

traceShow x = trace (show x) x

traceShowV msg x = trace (msg ++ ": " ++ show x) x
