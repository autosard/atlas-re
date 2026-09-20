module CostAnalysis.TemplateLanguage
  ( TemplateLanguage
  , TemplateLanguageConfig
  , AtomicLangConfig (..)
  , defaultTLang
  , sizeTLang
  , fromConfig
  , genBinoms
  ) where

import Data.Set(Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.MultiSet as MSet

import Syntax (Id)
import Syntax.ResourceExpression
import qualified Syntax.FreeModule as FM


type TemplateLanguageConfig = [AtomicLangConfig]

data AtomicLangConfig
  = SizeLangConf 
  | LogLangConf Int Int
  | BinomLangConf Int
  | PotLangConf
  | LinLogConf 
  deriving (Eq, Show)

defaultLangConfig = [LogLangConf 1 2, BinomLangConf 2, PotLangConf]

type TemplateLanguage = [Id] -> Set ResourceTerm


mergeLangs :: TemplateLanguage -> TemplateLanguage -> TemplateLanguage
mergeLangs f g args = f args `S.union` g args

fromConfig :: TemplateLanguageConfig -> TemplateLanguage
fromConfig = foldr (mergeLangs . fromAtomConf) (const S.empty)

fromAtomConf :: AtomicLangConfig -> TemplateLanguage
fromAtomConf SizeLangConf args = S.fromList $ RTId : [RTSize x | x <- args]
fromAtomConf PotLangConf args = S.fromList $ map RTPhi args
fromAtomConf (LogLangConf a b) args =
  S.fromList $ RTId : map RTLog (genSizeSums (a,b) args)
fromAtomConf (BinomLangConf k) args = S.fromList $ genBinoms k args
fromAtomConf LinLogConf args = S.fromList $ RTId :
  [RTProd $ MSet.fromList [RTSize x, RTLog sx]
  | x   <- args,
    sx <- genSizeSums (1,1) [x]]

genSizeSums :: (Int, Int) -> [Id] -> [SizeExpr]
genSizeSums (a,b) xs = [FM.add (FM.singleton' SId (fromIntegral c)) vars
                       | vars <- varSums xs,
                         c <- [-1..b],                
                         sum vars + fromIntegral c >= 1,
                         not (M.null vars && c == 2)] -- log(2) covered by RTId
  where
    varSums :: [Id] -> [Map SizeTerm Rational]
    varSums [] = [M.empty]
    varSums (x:xs) = [if k > 0
                      then M.insert (SVar x) (fromIntegral k) ys
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
             n -> RTBinom (FM.singleton (SVar x)) n : bs
          | a <- [0..k]
          , bs <- genBinomProds xs (k - a)]


defaultTLang :: TemplateLanguage
defaultTLang = fromConfig defaultLangConfig

sizeTLang :: TemplateLanguage
sizeTLang = fromAtomConf SizeLangConf


