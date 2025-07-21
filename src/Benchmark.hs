{-# LANGUAGE OverloadedStrings #-}

module Benchmark where

import Ast
import Text.Megaparsec (SourcePos(SourcePos), mkPos)
import qualified Data.Text as T
import Typing.Inference (inferExpr)
import System.Exit (die)
import qualified Data.List as L
import System.Random (randomRIO)
import Control.Monad (replicateM)
import Control.Monad.State
import Data.IntMap (IntMap)
import qualified Data.IntMap as M

defaultAnn = SourcePos "bench" (mkPos 1) (mkPos 1)

genBenchmark :: String -> [String] -> TypedModule -> IO TypedExpr
genBenchmark bench args ctx = do
  e <- pickBenchmark bench args 
  case inferExpr ctx e of
    Left srcErr -> die "type error"
    Right expr -> return expr

pickBenchmark :: String -> [String] -> IO ParsedExpr
pickBenchmark "sort" [n] = return $ sort (read n)
pickBenchmark "rsort" [n] = rsort (read n)
-- pickBenchmark "golden_sort" [n] = return $ sort' (read n)
pickBenchmark "golden_delmin" [n] = return $ delmin (read n)
-- pickBenchmark "g" [n] = return $ g (read n)
-- pickBenchmark "gtree" [n] = return $ mkGolden (read n)
pickBenchmark _ _ = die "invalid benchmark configuration"

sort :: Int -> ParsedExpr
sort n = AppAnn defaultAnn "sort" [convertList [1..n]]

rsort :: Int -> IO ParsedExpr
rsort n = (\l -> AppAnn defaultAnn "sort" [convertList l]) <$> randList n

-- sort' n = let nil = ConstAnn defaultAnn "nil" [] in
--   AppAnn defaultAnn "removes" [g n, nil]

delmin n = let nil = ConstAnn defaultAnn "nil" [] in
  AppAnn defaultAnn "removes" [mkGolden n, nil]
  
convertList :: [Int] -> ParsedExpr
convertList [] = ConstAnn defaultAnn "nil" []
convertList (x:xs) = let x' = ConstAnn defaultAnn (T.pack $ "num#" ++ show x) [] in
                         ConstAnn defaultAnn "cons" [x', convertList xs]

randList :: Int -> IO [Int]
randList n = replicateM n $ randomRIO (1,n::Int)
                    

-- g :: Int -> ParsedExpr
-- g n = g' n n (-n)

-- g' :: Int -> Int -> Int -> ParsedExpr
-- g' lim 0 _ = ConstAnn defaultAnn "leaf" []
-- g' lim 1 lab = let t = ConstAnn defaultAnn "leaf" []
--                    lab' = ConstAnn defaultAnn (T.pack $ "num#" ++ show lab) [] in
--   ConstAnn defaultAnn "node" [t, lab', t]
-- g' lim n lab = let t = g' lim (l n) lab
--                    u = g' lim (r n) (-l ((-lab) - 1)) in
--                           AppAnn defaultAnn "meld" [t, u]

fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

mkGolden :: Int -> ParsedExpr
mkGolden 0 = ConstAnn defaultAnn "leaf" []
mkGolden n = 
  let a = ConstAnn defaultAnn (T.pack $ "num#" ++ show (-n)) []
      t = mkGolden $ l (n-1)
      u = mkGolden $ r (n-1) in
  ConstAnn defaultAnn "node" [t, a, u]

median :: [Rational] -> Rational
median l = head $ middle $ L.sort l  

middle :: [a] -> [a]
middle l@(_:_:_:_) = middle $ tail $ init l
middle l           = l

findK n k = if fibs!!k <= n && n < fibs!!(k + 1) 
            then k
            else findK n (k+1)

logPhi = logBase 1.618

nLargest :: Integral b => Int -> b
nLargest f = floor (logPhi (sqrt 5 * (fromIntegral f + 1/2)))              

l :: Int -> Int
l 0 = 0
l n = let k = nLargest n in
  fibs !! (k - 1) + l (n - (fibs !! k))

r :: Int -> Int
r 0 = 0
r n = let k = nLargest n in
  fibs !! (k - 2) + r (n - (fibs !! k))

