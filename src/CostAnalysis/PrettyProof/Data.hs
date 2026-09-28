{-# LANGUAGE OverloadedStrings #-}

-- | Converts an 'AnalysisResult' into the JSON document the proof viewer
-- renders.
module CostAnalysis.PrettyProof.Data
  ( proofData
  , proofSourceFiles
  ) where

import Data.Aeson (Value, object, (.=), toJSON)
import Data.Char (toLower)
import Data.List (intercalate, nub, mapAccumL)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Tree as Tr
import Text.Megaparsec (SourcePos (..), unPos)

import Syntax (Id)
import Syntax.Annotation (HasAnnotation (..), PositionedExprAnn (..), ExprSrc (..))
import Syntax.PrettyPrint (prettyPrint)
import Syntax.Program (FunDef (..))
import Syntax.Measure (SizeTransform (..), ConstPat (..))
import qualified Syntax.Measure as Measure (Relation (..))
import CostAnalysis.Analysis (AnalysisResult (..))
import CostAnalysis.Coeff (Coeff (..), instCoeffs)
import CostAnalysis.Constraint (Formula (..), ArithExpr (..))
import CostAnalysis.ProveMonad (Derivation, OptBound (..))
import CostAnalysis.Rules
import CostAnalysis.Template
  ( FreeTemplate (..), FreeSig (..), BoundTemplate (..), Template (amortisedCost) )
import CostAnalysis.PrettyProof.Format

--------------------------------------------------------------------------------
-- Intermediate tree
--------------------------------------------------------------------------------

data Node = Node
  { nKind :: String
  , nRule :: String
  , nJt :: Maybe String
  , nExpr :: String
  , nSrc :: Maybe (SourcePos, Bool) -- ^ position and whether it is derived
  , nQ :: Maybe FreeTemplate
  , nQ' :: Maybe FreeTemplate
  , nCs :: [Formula]
  , nWeak :: Bool
  }

fromRuleApp :: RuleApp -> Node
fromRuleApp (ExprRuleApp rule info) = Node
  { nKind = ruleKind rule
  , nRule = ruleLabel rule
  , nJt = jtLabel (_raJt info)
  , nExpr = shortExpr (prettyPrint (_raExpr info))
  , nSrc = srcOf (peSrc (getAnn (_raExpr info)))
  , nQ = Just (_raQ info)
  , nQ' = Just (_raQ' info)
  , nCs = _raCs info
  , nWeak = case rule of Sub _ -> True; _ -> False
  }
fromRuleApp (MatchArmApp pat info) = Node
  { nKind = "case"
  , nRule = "case"
  , nJt = jtLabel (_raJt info)
  , nExpr = showPattern pat
  , nSrc = srcOf (peSrc (getAnn pat))
  , nQ = Just (_raQ info)
  , nQ' = Just (_raQ' info)
  , nCs = _raCs info
  , nWeak = False
  }
fromRuleApp (FunRuleApp def) = Node
  { nKind = "fn"
  , nRule = "fn"
  , nJt = Nothing
  , nExpr = unwords (map T.unpack (_funName def : _funArgs def))
  , nSrc = srcOf (peSrc (getAnn (_funBody def)))
  , nQ = Nothing
  , nQ' = Nothing
  , nCs = []
  , nWeak = False
  }

-- | Positions in real source files; synthetic ones (e.g. @<elab>@) are dropped.
srcOf :: ExprSrc -> Maybe (SourcePos, Bool)
srcOf src = case src of
  Loc p -> real p False
  DerivedFrom p -> real p True
  where real p derived
          | take 1 (sourceName p) == "<" = Nothing
          | otherwise = Just (p, derived)

ruleKind :: Rule -> String
ruleKind (Sub _) = "sub"
ruleKind IteCoin = "ite"
ruleKind r = map toLower (show r)

ruleLabel :: Rule -> String
ruleLabel (Sub args) = "sub [" ++ intercalate "," (map (map toLower . show) args) ++ "]"
ruleLabel r = map toLower (show r)

jtLabel :: JudgementType -> Maybe String
jtLabel Standard = Nothing
jtLabel jt = Just (show jt)

shortExpr :: String -> String
shortExpr s = let line = takeWhile (/= '\n') s in
  if length line > 120 then take 117 line ++ "…" else line

--------------------------------------------------------------------------------
-- Encoding
--------------------------------------------------------------------------------

data Ctx = Ctx
  { cInCore :: Formula -> Bool
  , cKnown :: Map Coeff Rational
  }

encodeTree :: Ctx -> Tr.Tree (Int, Node) -> Value
encodeTree ctx (Tr.Node (i, n) kids) = object
  [ "id" .= i
  , "kind" .= nKind n
  , "rule" .= nRule n
  , "jt" .= nJt n
  , "expr" .= nExpr n
  , "pos" .= fmap (\(p, _) -> [unPos (sourceLine p), unPos (sourceColumn p)]) (nSrc n)
  , "file" .= fmap (sourceName . fst) (nSrc n)
  , "derived" .= maybe False snd (nSrc n)
  , "qi" .= fmap _ftId (nQ n)
  , "qo" .= fmap _ftId (nQ' n)
  , "rows" .= [ (crTerm r, crLhs r, crOp r, crRhs r, core)
              | (r, core) <- rows, not (crWeakNonNeg r) ]
  , "hidden" .= length [() | (r, _) <- rows, crWeakNonNeg r]
  , "core" .= length (filter snd rows)
  , "weak" .= if nWeak n then Just (encodeWeak (nCs n)) else Nothing
  , "kids" .= map (encodeTree ctx) kids
  ]
  where rows = [(constraintRow f, cInCore ctx f) | f <- nCs n]

encodeWeak :: [Formula] -> Value
encodeWeak cs = object
  [ "mono" .= [enc w | w <- ws, wvIsMono w]
  , "ax" .= [enc w | w <- ws, not (wvIsMono w)]
  ]
  where ws = weakeningVars cs
        enc w = (wvVar w, wvSmaller w, wvLarger w)

encodeTemplate :: Ctx -> FreeTemplate -> Value
encodeTemplate ctx q = object
  [ "terms" .= map showTerm terms
  , "vals" .= if any (`M.member` cKnown ctx) coeffs
      then Just [maybe "?" showRat (cKnown ctx M.!? c) | c <- coeffs]
      else Nothing
  ]
  where terms = S.toList (_ftTerms q)
        coeffs = map (Coeff (_ftId q)) terms

-- | The template with known values bound, when any of its values is known.
boundOf :: Ctx -> FreeTemplate -> Maybe BoundTemplate
boundOf ctx q
  | any (`M.member` cKnown ctx) coeffs = Just . BoundTemplate $ M.fromList
      [(t, M.findWithDefault 0 (Coeff (_ftId q) t) (cKnown ctx)) | t <- terms]
  | otherwise = Nothing
  where terms = S.toList (_ftTerms q)
        coeffs = map (Coeff (_ftId q)) terms

-- | Values fixed by equations @Q_i[t] = c@, i.e. a declared annotation.
declaredValues :: [Formula] -> Map Coeff Rational
declaredValues cs = M.fromList $ mapMaybe go cs
  where go (Eq (CoeffTerm c) (ConstTerm v)) = Just (c, v)
        go (Eq (ConstTerm v) (CoeffTerm c)) = Just (c, v)
        go _ = Nothing

numberTrees :: Int -> [Tr.Tree a] -> (Int, [Tr.Tree (Int, a)])
numberTrees = mapAccumL (mapAccumL (\i x -> (i + 1, (i, x))))

showSizeTransform :: Id -> SizeTransform -> String
showSizeTransform fn (SizeTransform lhs rhs rel) =
  "|" ++ unwords (map T.unpack (fn : lhs)) ++ "| " ++ op ++ " " ++ showSize rhs
  where op = case rel of
          Measure.Ge -> "≤"
          Measure.Eq -> "="

--------------------------------------------------------------------------------
-- Document
--------------------------------------------------------------------------------

proofData :: Map FilePath [Text] -> AnalysisResult -> Value
proofData sources result = object
  [ "result" .= (if sat then "sat" else "unsat" :: String)
  , "objective" .= objective
  , "file" .= listToMaybe (nodeFiles result)
  , "functions" .= (snd (mapAccumL encodeFn firstId fnNames) ++ globalFn)
  , "potentials" .= map encodePot (M.toList (_arPotSig result))
  , "templates" .= M.fromList [(show (_ftId q), encodeTemplate ctx q) | q <- allTemplates]
  , "sources" .= sources
  ]
  where
    (sat, core, solution, objective) = case _arResult result of
      Left cs -> (False, S.fromList cs, Nothing, Nothing)
      Right (sol, OptBound o) -> (True, S.empty, Just sol, Just o)
    ctx = Ctx
      { cInCore = (`S.member` core)
      , cKnown = fromMaybe (declaredValues (_arSigCs result)) solution
      }
    sigs = _arSig result
    derivs = _arDerivs result
    fnNames = S.toList (M.keysSet sigs <> M.keysSet derivs)

    sigTemplates fs = S.fromList [_ftId (_fsFrom fs), _ftId (_fsTo fs)]
    ownsCs fs f = not . S.null $ S.intersection (sigTemplates fs) (coeffIds f)
    sigCsOf fn = case M.lookup fn sigs of
      Just fs -> filter (ownsCs fs) (_arSigCs result)
      Nothing -> []
    globalCs = [f | f <- _arSigCs result, not (any (`ownsCs` f) (M.elems sigs))]

    firstId = 0 :: Int
    encodeFn i fn =
      let fs = M.lookup fn sigs
          (i', trees) = numberTrees (i + 1) (map (fmap fromRuleApp) (M.findWithDefault [] fn derivs))
          rootNode = Node
            { nKind = "fn", nRule = "fn", nJt = Nothing
            , nExpr = unwords (map T.unpack (fn : maybe [] _fsFormArgs fs))
            , nSrc = listToMaybe [s | Tr.Node (_, n) _ <- trees, Just s <- [nSrc n]]
            , nQ = _fsFrom <$> fs, nQ' = _fsTo <$> fs
            , nCs = sigCsOf fn, nWeak = False }
          root = encodeTree ctx (Tr.Node (i, rootNode) trees)
      in (i', encodeFunction fn fs root)

    globalFn
      | null globalCs = []
      | otherwise = [object
          [ "name" .= ("global" :: String)
          , "args" .= ([] :: [String])
          , "tree" .= encodeTree ctx (Tr.Node (-1, globalNode) [])
          ]]
    globalNode = Node "fn" "fn" Nothing "global constraints" Nothing Nothing Nothing globalCs False

    encodeFunction fn fs root = object $
      [ "name" .= fn
      , "tree" .= root
      , "size" .= fmap (showSizeTransform fn) (M.lookup fn (_arSizeSig result))
      ] ++ case fs of
        Nothing -> []
        Just s ->
          [ "args" .= _fsFormArgs s
          , "binder" .= _fsBinder s
          , "from" .= _ftId (_fsFrom s)
          , "to" .= _ftId (_fsTo s)
          , "pre" .= fmap (showBound . btCoeffs) (boundOf ctx (_fsFrom s))
          , "post" .= fmap (showBound . btCoeffs) (boundOf ctx (_fsTo s))
          , "cost" .= fmap (showBound . btCoeffs . amortisedCost) (boundOf ctx (_fsFrom s))
          ]

    encodePot (scheme, clauses) = object
      [ "type" .= prettyPrint scheme
      , "clauses" .= [ (unwords (map T.unpack (c : args)), showRScalarExpr (inst e))
                     | (ConstPat c args, e) <- clauses ]
      ]
    inst e = maybe e (`instCoeffs` e) solution

    allTemplates = nubOn _ftId $
      concatMap (\fs -> [_fsFrom fs, _fsTo fs]) (M.elems sigs)
      ++ concatMap (concatMap (concatMap ruleTemplates . Tr.flatten)) (M.elems derivs)

ruleTemplates :: RuleApp -> [FreeTemplate]
ruleTemplates (ExprRuleApp _ info) = [_raQ info, _raQ' info]
ruleTemplates (MatchArmApp _ info) = [_raQ info, _raQ' info]
ruleTemplates (FunRuleApp _) = []

nubOn :: Ord b => (a -> b) -> [a] -> [a]
nubOn f = go S.empty
  where go _ [] = []
        go seen (x : xs)
          | S.member (f x) seen = go seen xs
          | otherwise = x : go (S.insert (f x) seen) xs

nodeFiles :: AnalysisResult -> [FilePath]
nodeFiles result = nub
  [ sourceName (fst s)
  | ds <- M.elems (_arDerivs result)
  , d <- ds
  , app <- Tr.flatten (d :: Derivation)
  , Just s <- [nSrc (fromRuleApp app)] ]

-- | The source files the derivations point into, for embedding them.
proofSourceFiles :: AnalysisResult -> [FilePath]
proofSourceFiles = nodeFiles
