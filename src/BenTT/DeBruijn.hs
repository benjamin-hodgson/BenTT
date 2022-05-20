{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}

module BenTT.DeBruijn (
    Subst,
    suc,
    hoas,
    deBruijn,
    addToSubst,
    applySubst,
    emptySubst,
    unsafeClosed, unsafeClosed'
) where

import Optics (Iso, iso, (&), traversed, (%), _2, (%~))
import Bound
import Bound.Name
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Maybe
import GHC.Generics
import Bound.Scope
import Data.Bifunctor

-- suc :: Term n -> Term (Var () n)
suc :: Functor f => f n -> f (Var b n)
suc = fmap F

hoas :: Monad f => (f (Var () n) -> f (Var () n)) -> Scope () f n
hoas f = toScope $ f $ pure (B ())

deBruijn :: (Monad f, Monad f') => Iso (Scope b f a) (Scope b' f' a') (f (Var b a)) (f' (Var b' a'))
deBruijn = iso fromScope toScope

newtype Subst f n = Subst { unSubst :: [(n, f n)] }
    deriving (Show, Read, Eq, Functor, Foldable, Traversable, Generic)

emptySubst = Subst []

addToSubst :: (Eq n, Monad f) => n -> f n -> Subst f n -> Subst f n
addToSubst n x (Subst subst) = Subst $ (n, x) : subst & traversed % _2 %~ substitute n x

applySubst :: (Eq n, Monad f) => Subst f n -> f n -> f n
applySubst s m = foldr (uncurry substitute) m (unSubst s)

unsafeClosed :: Traversable f => f n -> f m
unsafeClosed = fromJust . closed

unsafeClosed' :: Traversable f => f String -> f m
unsafeClosed' = unsafeClosed'
