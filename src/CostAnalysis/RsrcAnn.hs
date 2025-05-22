{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CostAnalysis.RsrcAnn where

import Prelude hiding (sum, or, and)

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
import Ast (CoeffAnnotation)
import Data.Map.Merge.Strict (merge, zipWithMatched, mapMissing)

data RsrcAnn = RsrcAnn {
  _annId :: Int,
  _args :: [Id],
  _label :: Text, -- ^ Human readable label, e.g. \"Q\", \"P\", ...
  _comment ::  Text, -- ^ Human readable comment, to trace the origin of the coefficient.
  _coeffs :: Set CoeffIdx -- ^ non zero coefficients
  }
  deriving (Eq, Show)

makeLenses ''RsrcAnn

type AnnCtx = Map Type RsrcAnn

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
annVars = _args

substArg :: Id -> Id -> RsrcAnn -> RsrcAnn
substArg x y q = q
  & args .~ args'
  & coeffs %~ S.map (substitute (q ^. args) args') 
  where args' = map (\z -> if z == x then y else z) $ q ^. args

bindAnn :: RsrcAnn -> Map Coeff Rational -> BoundAnn
bindAnn q values = BoundAnn (q^.args) $ M.fromList
  [(i, v) |
    c@(Coeff _ _ _ i) <- getCoeffs q,
    let v = fromMaybe 0 (values M.!? c)]

class (Show a) => AnnLike a where
  infixl 9 !
  (!) :: (Index i, Show i) => a -> i -> Term
  infixl 9 !?
  (!?) :: (Index i, Show i) => a -> i -> Term
  definedIdxs :: a -> Set CoeffIdx
  argVars :: a -> [Id]
  annEmpty :: a -> Bool

instance AnnLike RsrcAnn where
  argVars = annVars
  definedIdxs q = q^.coeffs
  annEmpty = S.null . _coeffs
  (!) ann idx = case coeffForIdx ann (toIdx idx) of
    Just q -> CoeffTerm q
    Nothing -> error $ "Invalid index '" ++ show idx ++ "' for annotation '" ++ show ann ++ "'."
  (!?) :: (Index i, Show i) => RsrcAnn -> i -> Term
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
  toIdx = mixed

data PointWiseOp = PointWiseOp {
  opArgs :: [Id] ,
  opCoeffs :: Map CoeffIdx Term}
  deriving(Show)

instance AnnLike PointWiseOp where
  argVars = opArgs
  definedIdxs op =  M.keysSet $ opCoeffs op
  annEmpty = M.null . opCoeffs
  (!) op idx = opCoeffs op M.! toIdx idx
  (!?) op idx = fromMaybe (ConstTerm 0) $ opCoeffs op M.!? toIdx idx

data BoundAnn = BoundAnn [Id] (Map CoeffIdx Rational)
  deriving (Show)

instance AnnLike BoundAnn where
  argVars (BoundAnn args _) = args
  definedIdxs (BoundAnn _ m) = M.keysSet m
  annEmpty (BoundAnn _ m) = M.null m
  (!) (BoundAnn _ m) idx = ConstTerm $ m M.! toIdx idx
  (!?) (BoundAnn _ m) idx = ConstTerm $ fromMaybe 0 (m M.!? toIdx idx)
  

instance AnnLike (Map CoeffIdx Rational) where
  argVars m = []
  definedIdxs = M.keysSet
  annEmpty = M.null 
  (!) m idx = ConstTerm $ m M.! toIdx idx
  (!?) m idx = ConstTerm $ fromMaybe 0 (m M.!? toIdx idx)

-- runWithZero :: (AnnLike a) => (a -> c) -> (k -> a -> c) 
-- runWithZero zipper = const (`zipper` pointWiseZero) 
--   where pointWiseZero = PointWiseOp [] M.empty

pointWiseZero = PointWiseOp [] M.empty

ctxZipWith :: (AnnLike a, AnnLike b) => (Type -> a -> c) -> (Type -> b -> c) -> (Type -> a -> b -> c) -> Map Type a -> Map Type b -> Map Type c
ctxZipWith fL fR zipper = merge missingStrategyL missingStrategyR (zipWithMatched (zipper))
  where missingStrategyL = mapMissing fL
        missingStrategyR = mapMissing fR


ctxScalarMul :: (AnnLike a) => Map Type a -> Term -> Map Type PointWiseOp
ctxScalarMul qs k = M.map (`annLikeScalarMul` k) qs

annLikeScalarMul :: (AnnLike a) => a -> Term -> PointWiseOp
annLikeScalarMul q k = PointWiseOp (argVars q) $
  M.fromList [(idx, prod2 (q!idx) k) | idx <- S.toList (definedIdxs q)]

annLikeAdd :: (AnnLike a, AnnLike b) => a -> b -> PointWiseOp
annLikeAdd q p | argVars q == argVars p = PointWiseOp (argVars q) $
             M.fromList [(idx, sum [q!?idx, p!?idx])
                        | idx <- S.toList $ definedIdxs q `S.union` definedIdxs p]
               | otherwise = error "point wise operation not valid for annotation likes with different arguments."
               
ctxAdd :: (AnnLike a, AnnLike b) => Map Type a -> Map Type b -> Map Type PointWiseOp
ctxAdd = ctxZipWith
  (const (`annLikeAdd` pointWiseZero))
  (const (annLikeAdd pointWiseZero))
  (const annLikeAdd)

ctxConstEq :: AnnLike a => Map Type a -> Map Type CoeffAnnotation -> [Constraint]
ctxConstEq ctx values = concat . M.elems $ ctxZipWith
  (const (`annLikeConstEq` M.empty))
  (const (annLikeConstEq pointWiseZero))
  (const annLikeConstEq) ctx values

ctxConstLe :: AnnLike a => Map Type a -> Map Type CoeffAnnotation -> [Constraint]
ctxConstLe ctx values = concat . M.elems $ ctxZipWith
  (const (`annLikeConstLe` M.empty))
  (const (annLikeConstLe pointWiseZero))
  (const annLikeConstLe) ctx values

annLikeUnify :: (AnnLike a, AnnLike b) => a -> b -> [Constraint]
annLikeUnify q p = concat [eq (q!?idx) p'
                          | idx <- S.toList $ definedIdxs q,
                            let p' | justConst idx = p!?idx 
                                   | length (argVars q) == length (argVars p) 
                                  = p!?substitute (argVars q) (argVars p) idx
                                   | otherwise = ConstTerm 0]

annLikeLeftInRight :: (AnnLike a, AnnLike b) => a -> b -> [Constraint]
annLikeLeftInRight q p = concat [or $ and (zero (q!?idx)) ++ and (ge p' (q!?idx))
                          | idx <- S.toList $ definedIdxs q,
                            let p' | justConst idx = p!?idx
                                   | otherwise =
                                     p!?substitute (argVars q) (stubArgVars (argVars p) $ length (argVars q)) idx]


ctxUnify :: (AnnLike a, AnnLike b) => Map Type a -> Map Type b -> [Constraint]
ctxUnify qs ps = concat . M.elems $ ctxZipWith
  (const (`annLikeUnify` pointWiseZero))
  (const (annLikeUnify pointWiseZero))
  (const annLikeUnify) qs ps

annLikeMap :: (AnnLike a, AnnLike b) => a -> b -> (CoeffIdx -> Maybe CoeffIdx) -> PointWiseOp
annLikeMap q p unifier = PointWiseOp (argVars p) (M.fromList coeffs')
  where coeffs' = [ (idx', q!idx)
                  | (Just idx', idx) <- zip (map unify qs) qs]
        unify = unifier . substitute (argVars q) (argVars p)
        qs = S.toList $ definedIdxs q
                  
annLikeUnify' :: (AnnLike a, AnnLike b) => a -> b -> [Id] -> [Constraint]
annLikeUnify' q p qArgs = concat [eq (q!?idx) (p!?substitute qArgs (argVars p) idx)
                                 | idx <- S.toList $ definedIdxs q]

ctxUnify' :: (AnnLike a, AnnLike b) => Map Type a -> Map Type b -> Map Type [Id] -> [Constraint]
ctxUnify' qs ps' args = concat . M.elems $ ctxZipWith
  (\t q -> annLikeUnifyForType t q pointWiseZero)
  (`annLikeUnifyForType` pointWiseZero)
  annLikeUnifyForType qs ps'
  where annLikeUnifyForType :: (AnnLike a, AnnLike b) => Type -> a -> b -> [Constraint]
        annLikeUnifyForType t q p = annLikeUnify' q p (args M.! t)

ctxEqSum :: (AnnLike a, AnnLike b) => Map Type a -> Map Type b -> [Constraint]
ctxEqSum qs ps = concat . M.elems $ ctxZipWith
  (const (`annLikeEqSum` pointWiseZero))
  (const (annLikeEqSum pointWiseZero))
  (const annLikeEqSum) qs ps

annLikeEqSum :: (AnnLike a, AnnLike b) => a -> b -> [Constraint]
annLikeEqSum q p | definedIdxs q == definedIdxs p
  = eq
    (sum [q!idx | idx <- S.toList $ definedIdxs q])
    (sum [p!idx | idx <- S.toList $ definedIdxs p])
                 | otherwise = error "Sum of coeffs is only defined for annotations with the same indicies."

type AnnArray = Map CoeffIdx RsrcAnn

elems :: AnnArray -> [RsrcAnn]
elems = M.elems

infixl 9 !!
(!!) :: AnnArray -> CoeffIdx -> RsrcAnn
(!!) arr k = case M.lookup k arr of
  Just c -> c
  Nothing -> error $ "Invalid index '" ++ show k ++ "' for annotation array."

data FunRsrcAnn = FunRsrcAnn {
  withCost :: (AnnCtx, AnnCtx),
  withoutCost :: [(AnnCtx, AnnCtx)],
  worstCase :: Bool}
  deriving(Show)

type RsrcSignature = Map Id FunRsrcAnn

type CoeffDef s a = State s a

def :: Index i => i -> CoeffDef RsrcAnn Term
def i = do
  let idx = toIdx i
  coeffs %= (idx `S.insert`)
  ann <- get
  return $ ann!idx

chainDef :: [RsrcAnn -> (RsrcAnn, [Constraint])] -> RsrcAnn -> (RsrcAnn, [Constraint])
chainDef fs q_ = foldr go (q_, []) fs
  where go f (q, css) = let (q', cs) = f q in
          (q', cs ++ css)

defMulti :: Index i => [(Type, i)] -> CoeffDef AnnCtx [Term]
defMulti = mapM go
  where go :: Index i => (Type, i) -> CoeffDef AnnCtx Term
        go (t, i) = do
          let idx = toIdx i
          ix t . coeffs %= (idx `S.insert`)
          ann <- gets (M.! t)
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
        
extendAnns :: AnnArray -> [CoeffDef AnnArray [a]] -> (AnnArray, [a])
extendAnns arr defs = (arr', concat cs)
  where (cs, arr') = runState def arr
        def = sequence defs

extendCtx :: AnnCtx -> CoeffDef AnnCtx [a] -> (AnnCtx, [a])
extendCtx ctx def = (ctx', cs)
  where (cs, ctx') = runState def ctx

  
ctxDefineFrom :: AnnCtx -> AnnCtx -> (AnnCtx, [Constraint])
ctxDefineFrom qs ps_ = foldr go (M.empty, []) (M.keys ps_)
  where go :: Type -> (AnnCtx, [Constraint]) -> (AnnCtx, [Constraint])
        go t (ps, css) = let (p', cs) = defineFrom (qs M.! t) (ps_ M.! t) in
                           (M.insert t p' ps, css ++ cs)

-- | @'defineFrom' q p@ Define q from p. This sets q(x) = p(x), where x contains only variables from q. 
defineFrom :: RsrcAnn -> RsrcAnn -> (RsrcAnn, [Constraint])
defineFrom q p = let xs = annVars q in
  extendAnn q $
  [(`eq` (p!idx)) <$> def idx
  | idx@(Pure x) <- pures p,
    x `elem` xs]
  ++ 
  [(`eq` (p!idx)) <$> def idx
  | idx <- mixes p,
    onlyVarsOrConst idx xs]
               
annLikeGeZero :: AnnLike a => a -> [Constraint]
annLikeGeZero ann = concat [ge (ann!idx) $ ConstTerm 0 | idx <- S.toList $ definedIdxs ann]

ctxGeZero :: (AnnLike a) => Map Type a -> [Constraint]
ctxGeZero = M.foldr go []
  where go ann cs = cs ++ annLikeGeZero ann

annLikeZero :: AnnLike a => a -> [Constraint]
annLikeZero ann = concat [eq (ann!idx) $ ConstTerm 0
                           | idx <- S.toList $ definedIdxs ann]

ctxZero :: (AnnLike a) => Map Type a -> [Constraint]
ctxZero = M.foldr go []
  where go ann cs = cs ++ annLikeZero ann 

annLikeConstLe :: AnnLike a => a -> CoeffAnnotation -> [Constraint]
annLikeConstLe ann values = concat [le (ann!idx) $ ConstTerm (M.findWithDefault 0 idx values)
                                   | idx <- S.toList $ definedIdxs ann]                   

annLikeConstEq :: AnnLike a => a -> CoeffAnnotation -> [Constraint]
annLikeConstEq ann values = concat [eq (ann!idx) $ ConstTerm (M.findWithDefault 0 idx values)
                                   | idx <- S.toList $ definedIdxs ann]
                        
instance HasCoeffs RsrcAnn where
  getCoeffs ann = map (coeffFromAnn ann) $ S.toList (ann^.coeffs)

instance (HasCoeffs a, HasCoeffs b) => HasCoeffs (a,b) where
  getCoeffs (x,y) = getCoeffs x ++ getCoeffs y
  
instance HasCoeffs (Map Type RsrcAnn) where
  getCoeffs = M.foldr (\q coeffs -> coeffs ++ getCoeffs q) []

instance HasCoeffs FunRsrcAnn where
  getCoeffs :: FunRsrcAnn -> [Coeff]
  getCoeffs ann = (getCoeffs . withCost) ann ++ (getCoeffs . withoutCost) ann

instance HasCoeffs RsrcSignature where
  getCoeffs = concatMap getCoeffs . M.elems


-- | @'unify'@ returns a mapping between template indicies, unifying two templates.
-- 
-- For two potentials \(\Phi(V), \Psi(W)\), this enables to obtain \(\Psi(V)\), a potential
-- with the arguments of \(\Phi\), applied to \(\Psi\), which can be used to calculate
-- the amortized costs by subtracting \(\Phi(V) - \Psi(V)\). Typically we want this potential
-- to be expressed in terms of the original coefficients of \(\Phi\), which can be accomplished by
-- appyling the unfier to lookup the coefficients.
--
-- If the potentials have an equal number of arguments unification just maps the arguments by
-- their position.
-- In the case where \(|V| > |W|\), we rely on a definition from Sleator and Tarjan, where we
-- define the potential of collection of arguments as the sum of the individual potentials.
--
-- \[\Psi(x_1, \dots, x_n) = \Psi(x_1) + \dots + \Psi(x_n)\]
--
-- This allows us to apply a potential \(\Psi(x) \), defined for only one argument to multible
-- arguments.
--
-- __Example:__ When calculating the costs of the meld operation that merges to two heaps, the
-- potentials differ in the number of their arguements. 
--
-- \[\Phi(x,y) = \mathcal{A}_{\mathbb{merge}} + \Psi(x) + \Psi(y), \Psi(z) = \Psi(z)\]
-- after unificication we get
-- \[\Psi(x,y) = \Psi(x) + \Psi(y)\]
-- so
-- \[\Phi(x,y) - \Psi(x,y) = \mathcal{A}_{\mathbb{merge}}\]
unify :: (AnnLike a, AnnLike b) => a -> b -> Map CoeffIdx CoeffIdx
unify q p | length (argVars q) == length (argVars p) =
            let s = M.fromList (zip (argVars q) (argVars p)) in
              M.fromList [(i, substitute (argVars q) (argVars p) i) | i <- S.toList (definedIdxs q)]
unify q p = case argVars p of
              [] -> M.empty
              [y] -> M.fromList [(i, substitute (argVars q)
                                   (replicate (length (argVars q)) y) i) | i <- S.toList (definedIdxs q)]
              _ys_greater_xs -> error $ "cannot apply potential function " ++ show p ++ " to arguements " ++ show (argVars q)   
