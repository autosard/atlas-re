module Typing.Scheme where

import qualified Data.Map as M
import Data.Map (Map)

import Primitive(Id, PrettyPrint(..))
import Typing.Type(Type(TGen, TFun), unprod, match)
import Typing.Subst(Types(apply, tv))
import Data.List (intercalate)
import Data.Foldable (asum)


instance Types Scheme where
  apply s (Forall n t) = Forall n (apply s t)
  tv (Forall _ t) = tv t

data Scheme = Forall !Int !Type
  deriving (Eq, Ord, Show)

-- instance Show Scheme where
--   show (Forall _ t) = show t

toScheme :: Type -> Scheme
toScheme = Forall 0

tFunArgs :: Scheme -> [Type]
tFunArgs (Forall _ (TFun args _)) = unprod args

tFunResult :: Scheme -> Type
tFunResult (Forall 0 (TFun _ result)) = result

toType :: Scheme -> Type
toType (Forall _ t) = t


quantify :: [Id] -> Type -> Scheme
quantify vs t = Forall (length vs) (apply s t)
  where vs' = [v | v <- tv t, v `elem` vs]
        s = M.fromList $ zip vs' (map TGen [0..])
        
quantifyAll :: Type -> Scheme
quantifyAll t = quantify (tv t) t

findByType :: Type -> Map Scheme a -> Maybe a
findByType t m = asum $ map valForKey $ M.toList m
  where 
    valForKey (Forall _ k, v) = do
      k `match` t
      return v

instance PrettyPrint Scheme where
  prettyPrint (Forall n t) = "forall "
    ++ intercalate "," (map (\i -> "?" ++ show n) [1..n])
    ++ ". " ++ prettyPrint t
