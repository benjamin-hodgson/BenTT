{-# LANGUAGE OverloadedStrings #-}

module BenTT.Equiv (
    isContr,
    fibre,
    isEquiv,
    equiv,
    idIsEquiv,
    idEquiv,
    pathToEquiv,
    coeIsEquiv,
    coeEquiv
) where

import Control.Monad.Trans (lift)
import Prelude hiding (pi)

import Bound (Scope, abstract1, instantiate1)

import BenTT.DeBruijn (hoas, suc, suc2, suc3, suc4, unsafeClosed')
import BenTT.Paths (refl)
import BenTT.Syntax (
    arr,
    dlam,
    lam,
    path,
    pi,
    sig,
    Constraint(..),
    Face(..),
    Term(..)
    )


-- isContr (A : U) = Sig (x : A) ((y : A) -> y = x)
isContr = unsafeClosed' $ lam "A" U $
    sig "x" "A" $ pi "y" "A" $ path "A" "y" "x"

-- fibre (A B : U) (f : A -> B) (y : B) = Sig (x : A) (f x = y)
fibre = unsafeClosed' $ lam "A" U $ lam "B" U $
    lam "f" ("A" `arr` "B") $ lam "y" "B" $
        sig "x" "A" $ path "B" ("f" :$ "x") "y"

-- isEquiv (A B : U) (f : A -> B) = (y : B) -> isContr (fibre A B f y)
isEquiv = unsafeClosed' $ lam "A" U $ lam "B" U $
    lam "f" ("A" `arr` "B") $
        pi "y" "B" $
            isContr :$ (fibre :$ "A" :$ "B" :$ "f" :$ "y")

-- equiv (A B : U) = Sig (f : A -> B) (isEquiv A B f)
equiv = unsafeClosed' $ lam "A" U $ lam "B" U $
    sig "f" ("A" `arr` "B")
        (isEquiv :$ "A" :$ "B" :$ "f")

-- idIsEquiv (A : U) : IsEquiv A A id =
--   \(x : A) -> (
--     (x, refl x),
--     \(fib : fibre A A id x) <i> ->
--       let aux = <j> hcomp A 1 j x [i=0 |> snd fib, i=1 |> refl x]
--       in (aux 0, aux)
--   )
idIsEquiv = unsafeClosed' $ lam "A" U $
    lam "x" "A" (
        Pair
            (Pair "x" $ refl "x")
            (lam "fib" (fibre :$ "A" :$ "A" :$ idTm "A" :$ "x") $ dlam "i" $
                let aux = dlam "j" $
                        HComp "A" I1 "j" "x" [
                            ["i":=I0] :> abstract1 "k" (Snd "fib" :@ "k"),
                            ["i":=I1] :> lift "x"]
                in Pair (aux :@ I0) aux
            )
    )
    `Ann`
    (isEquiv :$ "A" :$ "A" :$ idTm "A")

idEquiv = unsafeClosed' $ lam "A" U $
    Pair (idTm "A") (idIsEquiv :$ "A")
    `Ann`
    (equiv :$ "A" :$ "A")

idTm a = Lam a $ hoas id

-- pathToEquiv (A B : U) (p : Path U A B) : equiv A B
--   = coe (i. equiv A (p@i)) 0 1 (idEquiv A)
pathToEquiv = unsafeClosed' $ lam "A" U $ lam "B" U $ lam "p" (path U "A" "B") $
    Coe (abstract1 "i" (equiv :$ "A" :$ ("p":@"i"))) I0 I1 (idEquiv :$ "A")
    `Ann`
    (equiv :$ "A" :$ "B")

-- coeIsEquiv (A : I -> U) (r r' : I) : isEquiv (\(x : A@r). coe A r r' x)
--   = coe (i. isEquiv (coe A r i)) r r' (idEquiv (A@r))
coeIsEquiv :: Scope () Term n -> Term n
coeIsEquiv a = DLam $ hoas $ \r -> DLam $ hoas $ \r' ->
    let a0 = suc $ instantiate1 r (suc a)
    in
        Coe
            (hoas $ \i -> isEquiv :$ Lam (suc a0) (hoas $ Coe (suc4 a) (suc3 r) (suc i)))
            (suc r)
            r'
            (idEquiv :$ a0)
        `Ann`
        (isEquiv :$ Lam a0 (hoas $ Coe (suc3 a) (suc2 r) (suc r')))

coeEquiv :: Scope () Term n -> Term n
coeEquiv a = DLam $ hoas $ \r -> DLam $ hoas $ \r' ->
    let a0 = suc $ instantiate1 r (suc a)
        a1 = instantiate1 r' (suc (suc a))
    in Pair (Lam a0 $ hoas $ Coe (suc3 a) (suc2 r) (suc r')) (coeIsEquiv (suc2 a) :@ suc r :@ r')
        `Ann`
        (equiv :$ a0 :$ a1)

