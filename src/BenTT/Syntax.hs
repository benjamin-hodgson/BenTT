{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module BenTT.Syntax (
    Type,
    Term(..),
    System,
    Constraint(..),
    Face(..),
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

import Control.Applicative (Applicative(..))
import Control.Monad (ap)
import Control.Monad.Trans (lift)
import Data.String (IsString(..))
import GHC.Generics (Generic, Generic1)
import Prelude hiding (pi)

import Bound (Scope(..), Var(F), abstract1, (>>>=))
import Data.Functor.Classes (Eq1, Read1, Show1)
import Data.Functor.Classes.Generic (FunctorClassesDefault(..))
import Optics (Iso, Traversal, (&), (%~), iso, Field1, Field2, Each(..), itraversalVL)

infixl 2 :@
infixl 2 :$
infix 0 :>
infix 1 :=


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
    -- NOTE: equality of dimension terms
    -- =================================
    -- Since the interval is not Kan, dimension terms can only appear syntactically in limited ways.
    -- Specifically, the only constructs which can be typed as I are I0, I1 and Var.
    -- There are never any redexes in the dimensional fragment of the language.
    -- That means, when comparing dimension terms for equality, we don't need to use `assertEqual` -
    -- we can get away with alpha equivalence `==`.
    -- So we don't need to be in the `Tc` monad to compare dimensions.
    | I
    | I0 | I1
    | Term n :@ Term n
    | DLam (Scope () Term n)
    | PathD (Scope () Type n) (Term n) (Term n)  -- PathD (<k> A) m n
    | Coe (Scope () Type n) (Term n) (Term n) (Term n)  -- coe (<k> A) r->r' x
    | HComp (Type n) (Term n) (Term n) (Term n) (System (Scope () Term) n) -- hcomp A r->r' x [i=j |> <k>y, ...]
    | Box (Term n) (Term n) (Term n) (System (Scope () Term) n)  -- hcomp U r->r' A [i=j |> <k>B, ...]
    | MkBox (Term n) (System Term n)  -- mkbox x [i=j |> y, ...]
    | Unbox (Term n) (Term n) (Term n)  -- Unbox r<-r' g
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault Term

type System f n = [Constraint f n]

data Constraint f n = [Face n] :> f n
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault (Constraint f)

instance Field1 (Constraint f n) (Constraint f n) [Face n] [Face n]
instance Field2 (Constraint f n) (Constraint g n) (f n) (g n)

data Face n = Term n := Term n
    deriving (Eq, Show, Read, Functor, Foldable, Traversable, Generic, Generic1)
    deriving (Eq1, Show1, Read1) via FunctorClassesDefault Face

instance Field1 (Face n) (Face n) (Term n) (Term n)
instance Field2 (Face n) (Face n) (Term n) (Term n)
instance Each (Either () ()) (Face n) (Face m) (Term n) (Term m) where
    each = itraversalVL $ \f (i:=j) -> liftA2 (:=) (f (Left ()) i) (f (Right ()) j)

bindSys :: (f n -> (n -> Term m) -> f m) -> (n -> Term m) -> System f n -> System f m
bindSys embed k sys = [[(i >>= k) := (j >>= k) | i:=j <- cof] :> embed x k | cof :> x <- sys]

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
    Coe ty r r' x >>= k = Coe
        (ty >>>= k)
        (r >>= k)
        (r' >>= k)
        (x >>= k)
    HComp ty r r' x sys >>= k = HComp
        (ty >>= k)
        (r >>= k)
        (r' >>= k)
        (x >>= k)
        (bindSys (>>>=) k sys)
    Box r r' a sys >>= k = Box
        (r >>= k)
        (r' >>= k)
        (a >>= k)
        (bindSys (>>>=) k sys)
    MkBox x sys >>= k = MkBox
        (x >>= k)
        (bindSys (>>=) k sys)
    Unbox r r' b >>= k = Unbox (r >>= k) (r' >>= k) (b >>= k)

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
