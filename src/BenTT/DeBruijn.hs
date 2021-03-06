{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}

module BenTT.DeBruijn (
    Subst,
    suc, suc2, suc3, suc4,
    hoas,
    deBruijn,
    xchg,
    xchgScope,
    addToSubst,
    appendSubst,
    applySubst,
    emptySubst,
    unsafeClosed, unsafeClosed'
) where

import Data.Maybe (fromJust)
import GHC.Generics (Generic)

import Bound (Scope, Var(..), fromScope, toScope, substitute, closed)
import Optics (Iso, iso, (&), (%~))

suc :: Functor f => f n -> f (Var b n)
suc = fmap F
suc2 :: Functor f => f n -> f (Var b1 (Var b2 n))
suc2 = suc . suc
suc3 :: Functor f => f n -> f (Var b1 (Var b2 (Var b3 n)))
suc3 = suc2 . suc
suc4 :: Functor f => f n -> f (Var b1 (Var b2 (Var b3 (Var b4 n))))
suc4 = suc3 . suc

hoas :: Monad f => (f (Var () n) -> f (Var () n)) -> Scope () f n
hoas f = toScope $ f $ pure (B ())

-- | Not really an isomorphism
deBruijn :: (Monad f, Monad f') => Iso (Scope b f a) (Scope b' f' a') (f (Var b a)) (f' (Var b' a'))
deBruijn = iso fromScope toScope

xchgScope :: Monad f => Scope b1 f (Var b2 n) -> Scope b2 f (Var b1 n)
xchgScope s = s & deBruijn %~ xchg

xchg :: Functor f => f (Var b1 (Var b2 n)) -> f (Var b2 (Var b1 n))
xchg = fmap f
    where
        f (B b) = F (B b)
        f (F (B b)) = B b
        f (F (F v)) = F (F v)

newtype Subst f n = Subst { unSubst :: [(n, f n)] }
    deriving (Show, Read, Eq, Functor, Foldable, Traversable, Generic)

emptySubst = Subst []

appendSubst :: (Eq n, Monad f) => Subst f n -> Subst f n -> Subst f n
appendSubst subst = foldr (uncurry addToSubst) subst . unSubst

addToSubst :: (Eq n, Monad f) => n -> f n -> Subst f n -> Subst f n
addToSubst n x (Subst subst) = Subst $ (n, x) : [(m, substitute n x y) | (m, y) <- subst]

applySubst :: (Eq n, Monad f) => Subst f n -> f n -> f n
applySubst s m = foldr (uncurry substitute) m (unSubst s)

unsafeClosed :: Traversable f => f n -> f m
unsafeClosed = fromJust . closed

unsafeClosed' :: Traversable f => f String -> f m
unsafeClosed' = unsafeClosed
