{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module BenTT.Syntax (
    (:*)(..),
    Type,
    Term(..),
    System,
    Constraint(..),
    Face(..), faceParts,
    pi,
    sig,
    prod,
    let_,
    lam,
    dlam,
    path,
    pathd,
    arr
) where

import Control.Applicative
import Control.Monad (ap)
import Control.Monad.Trans
import Data.Bifunctor
import Data.Maybe
import Data.String
import GHC.Generics
import Prelude hiding (pi)

import Bound
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Optics (Iso, iso, (&), (%~), Traversal, traversalVL)

import BenTT.DeBruijn

infixl 2 :@
infixl 2 :$
infix 0 :>
infix 1 :=

data (f :* g) x = f x :* g x
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault (f :* g)
bindPair :: Monad f => (f :* f) a -> (a -> f b) -> (f :* f) b
bindPair (f :* g) k = (f >>= k) :* (g >>= k)


type Type = Term
data Term n
    = Hole
    | U
    | Var n
    | Ann (Term n) (Type n)
    | Term n :$ Term n
    | Lam (Type n) (Scope () Term n)
    | Pi (Type n) (Scope () Type n)
    | Pair (Term n) (Term n)
    | Sig (Type n) (Scope () Type n)
    | Fst (Term n) | Snd (Term n)
    | Let (Type n) (Term n) (Scope () Term n)
    | I
    | I0 | I1
    | Term n :@ Term n
    | DLam (Scope () Term n)
    | PathD (Scope () Type n) (Term n) (Term n)  -- PathD (<k> A) m n
    | Coe (Scope () Type n) (Term n) (Term n) (Term n)  -- coe (<k> A) i->j x
    | HComp (Type n) (Term n) (Term n) (Term n) (System (Scope () Term) n) -- hcomp A i->j x [i=j |> <k>x, ...]
    | Glue (Type n) (System (Type :* Term) n)  -- Glue A [i=j |> (T, E), ...]
    | MkGlue (Term n) (System Term n)  -- glue x [i=j |> t, ...]
    | Unglue (Term n)  -- unglue g
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault Term

type System f n = [Constraint f n]

data Constraint f n = [Face n] :> f n
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault (Constraint f)

data Face n = Term n := Term n
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault Face

faceParts :: Traversal (Face n) (Face m) (Term n) (Term m)
faceParts = traversalVL $ \f (i:=j) -> liftA2 (:=) (f i) (f j)

bindSys :: (f n -> (n -> Term m) -> f m) -> (n -> Term m) -> System f n -> System f m
bindSys embed k sys = [[(i >>= k) := (j >>= k) | i:=j <- faces] :> embed x k | faces :> x <- sys]

instance Applicative Term where
    pure = Var
    (<*>) = ap

instance Monad Term where
    return = Var

    Hole >>= _ = Hole
    U >>= _ = U
    Var x >>= k = k x
    Ann x t >>= k = Ann (x >>= k) (t >>= k)
    (f :$ x) >>= k = (f >>= k) :$ (x >>= k)
    Lam ty b >>= k = Lam (ty >>= k) (b >>>= k)
    Pi d r >>= k = Pi (d >>= k) (r >>>= k)
    Pair x y >>= k = Pair (x >>= k) (y >>= k)
    Sig d r >>= k = Sig (d >>= k) (r >>>= k)
    Fst p >>= k = Fst (p >>= k)
    Snd p >>= k = Snd (p >>= k)
    Let x t b >>= k = Let (x >>= k) (t >>= k) (b >>>= k)
    I >>= _ = I
    I0 >>= _ = I0
    I1 >>= _ = I1
    (f :@ x) >>= k = (f >>= k) :@ (x >>= k)
    DLam b >>= k = DLam (b >>>= k)
    PathD t x y >>= k = PathD (t >>>= k) (x >>= k) (y >>= k)
    Coe ty i j x >>= k = Coe
        (ty >>>= k)
        (i >>= k)
        (j >>= k)
        (x >>= k)
    HComp ty i j x sys >>= k = HComp
        (ty >>= k)
        (i >>= k)
        (j >>= k)
        (x >>= k)
        (bindSys (>>>=) k sys)
    Glue ty sys >>= k = Glue
        (ty >>= k)
        (bindSys bindPair k sys)
    MkGlue x sys >>= k = MkGlue
        (x >>= k)
        (bindSys (>>=) k sys)
    Unglue x >>= k = Unglue (x >>= k)

pi :: Eq n => n -> Type n -> Type n -> Type n
pi name d r = Pi d (abstract1 name r)

sig :: Eq n => n -> Type n -> Type n -> Type n
sig name a b = Sig a (abstract1 name b)

prod :: Type n -> Type n -> Type n
prod a b = Sig a (lift b)

let_ :: Eq n => n -> Type n -> Term n -> Term n -> Term n
let_ name t x b = Let t x (abstract1 name b)

lam :: Eq n => n -> Type n -> Term n -> Term n
lam name ty b = Lam ty (abstract1 name b)

dlam :: Eq n => n -> Term n -> Term n
dlam name b = DLam (abstract1 name b)

path :: Term n -> Term n -> Term n -> Term n
path a = PathD (lift a)

pathd :: Eq n => n -> Term n -> Term n -> Term n -> Term n
pathd name f = PathD (abstract1 name f)

arr :: Term n -> Term n -> Term n
a `arr` b = Pi a (Scope (Var (F b)))
    
instance IsString (Term String) where
    fromString = Var
