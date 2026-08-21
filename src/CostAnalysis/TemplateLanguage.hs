module CostAnalysis.TemplateLanguage where

import Data.Set(Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.MultiSet as MSet

import Primitive(Id)
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size


type TemplateLanguageConfig = [AtomicLangConfig]

data AtomicLangConfig
  = SizeLangConf 
  | LogLangConf Int Int
  | BinomLangConf Int
  | RankLangConf
  deriving (Eq, Show)

defaultLangConfig = [LogLangConf 1 2, BinomLangConf 2, RankLangConf]

type TemplateLanguage = [Id] -> Set ResourceTerm


mergeLangs :: TemplateLanguage -> TemplateLanguage -> TemplateLanguage
mergeLangs f g args = f args `S.union` g args

fromConfig :: TemplateLanguageConfig -> TemplateLanguage
fromConfig = foldr (mergeLangs . fromAtomConf) (const S.empty)

fromAtomConf :: AtomicLangConfig -> TemplateLanguage
fromAtomConf SizeLangConf args = S.fromList $ RTId : [RTSize x | x <- args]
fromAtomConf RankLangConf args = S.fromList $ map RTPhi args
fromAtomConf (LogLangConf a b) args =
  S.fromList $ RTId : map RTLog (genSizeSums (a,b) args)
fromAtomConf (BinomLangConf k) args = S.fromList $ genBinoms k args

genSizeSums :: (Int, Int) -> [Id] -> [SizeSum]
genSizeSums (a,b) xs = [SizeSum vars c
                       | vars <- varSums xs,
                         c <- [-1..b],                
                         foldr (+) 0 vars + c >= 1,
                         not (M.null vars && c == 2)] -- log(2) covered by RTId
  where
    varSums :: [Id] -> [Map Id Int]
    varSums [] = [M.empty]
    varSums (x:xs) = [if k > 0
                      then M.insert x k ys
                      else ys
                     | k <- [0..a], ys <- varSums xs]

genBinoms :: Int -> [Id] -> [ResourceTerm]
genBinoms k xs = [case bs of
                    []  -> RTId
                    [b] -> b
                    ts -> RTProd (MSet.fromList ts)
                 | bs <-  genBinomProds xs k]
  where genBinomProds :: [Id] -> Int -> [[ResourceTerm]]
        genBinomProds xs 0 = [[]]
        genBinomProds [] _ = [[]]
        genBinomProds (x : xs) k =
          [case a of
             0 -> bs
             n -> RTBinom (sizeVar x) n : bs
          | a <- [0..k]
          , bs <- genBinomProds xs (k - a)]



defaultTLang :: TemplateLanguage
defaultTLang = fromConfig defaultLangConfig

sizeTLang :: TemplateLanguage
sizeTLang = fromAtomConf SizeLangConf


