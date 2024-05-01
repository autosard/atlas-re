module Typing.Scheme where

import qualified Data.Map as M

import Typing.Type(Type(TGen), Tyvar)
import Typing.Subst(Types(apply, tv))


instance Types Scheme where
  apply s (Forall n t) = Forall n (apply s t)
  tv (Forall _ t) = tv t

data Scheme = Forall !Int !Type
  deriving (Eq)

instance Show Scheme where
  show (Forall _ t) = show t

toScheme :: Type -> Scheme
toScheme = Forall 0

quantify :: [Tyvar] -> Type -> Scheme
quantify vs t = Forall (length vs) (apply s t)
  where vs' = [v | v <- tv t, v `elem` vs]
        s = M.fromList $ zip vs' (map TGen [0..])
        
