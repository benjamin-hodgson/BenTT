{-# LANGUAGE OverloadedStrings #-}

module BenTT.Equiv (isContr, fibre, isEquiv, equiv, idIsEquiv, idEquiv, pathToEquiv, refl) where

import Bound
import Control.Monad.Trans
import Data.Maybe
import BenTT.Syntax
import BenTT.DeBruijn
import Prelude hiding (pi)


-- isContr (A : U) = Sig (x : A) ((y : A) -> y = x)
isContr = closedTerm $ lam "A" U $
    sig "x" "A" $ pi "y" "A" $ path "A" "y" "x"

-- fibre (A B : U) (f : A -> B) (y : B) = Sig (x : A) (f x = y)
fibre = closedTerm $ lam "A" U $ lam "B" U $
    lam "f" ("A" `arr` "B") $ lam "y" "B" $
        sig "x" "A" $ path "B" ("f" :$ "x") "y"

-- isEquiv (A B : U) (f : A -> B) = (y : B) -> isContr (fibre A B f y)
isEquiv = closedTerm $ lam "A" U $ lam "B" U $
    lam "f" ("A" `arr` "B") $
        pi "y" "B" $
            isContr :$ (fibre :$ "A" :$ "B" :$ "f" :$ "y")

-- equiv (A B : U) = Sig (f : A -> B) (isEquiv A B f)
equiv = closedTerm $ lam "A" U $ lam "B" U $
    sig "f" ("A" `arr` "B")
        (isEquiv :$ "A" :$ "B" :$ "f")

-- idIsEquiv (A : U) : IsEquiv A A id =
--   \(x : A) -> (
--     (x, refl x),
--     \(fib : fibre A A id x) <i> ->
--       let aux = <j> hcomp A 1 j x [i=0 |> snd fib, i=1 |> refl x]
--       in (aux 0, aux)
--   )
idIsEquiv = closedTerm $ lam "A" U $
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

idEquiv = closedTerm $ lam "A" U $
    Pair (idTm "A") (idIsEquiv :$ "A")
    `Ann`
    (equiv :$ "A" :$ "A")

-- pathToEquiv (A B : U) (p : Path U A B) : equiv A B =
--   coe (i. equiv A (p@i)) 0 1 (idEquiv A)
pathToEquiv = closedTerm $ lam "A" U $ lam "B" U $ lam "p" (path U "A" "B") $
    Coe (abstract1 "i" (equiv :$ "A" :$ ("p":@"i"))) I0 I1 (idEquiv :$ "A")
    `Ann`
    (equiv :$ "A" :$ "B")

idTm a = Lam a $ hoas id
refl = DLam . lift

closedTerm :: Term String -> Term n
closedTerm = fromJust . closed

