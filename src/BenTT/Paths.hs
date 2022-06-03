{-# LANGUAGE OverloadedStrings #-}
module BenTT.Paths (
    refl,
    comp,
    funext,
    sym
) where

import Control.Monad.Trans
import Prelude hiding (pi)

import Bound
import Optics hiding ((:>))

import BenTT.DeBruijn (hoas, suc, unsafeClosed', deBruijn)
import BenTT.Syntax


refl :: Term n -> Term n
refl = DLam . lift

comp :: Scope () Type n -> Term n -> Term n -> Term n -> System (Scope () Term) n -> Term n
comp a i j x sys = HComp
    (instantiate1 j a)
    i j
    (Coe a i j x)
    [f :> y & deBruijn %~ Coe (suc a) (Var $ B ()) (suc j) | f :> y <- sys]

-- funext : (A B : U) (f g : A -> B)
--   ((x : A) -> Path B (f x) (g x))
--   -> Path (A -> B) f g
funextType :: Type n
funextType = unsafeClosed' $ pi "A" U $ pi "B" U $
    let ab = "A" `arr` "B"
    in pi "f" ab $ pi "g" ab $
        let proofTy = pi "x" "A" $ path "B" ("f" :$ "x") ("g" :$ "x")
        in proofTy `arr` path ab "f" "g"

-- funext = \(A B : U)
--     \(f g : A -> B)
--     \(p : (x : A) -> Path B (f x) (g x))
--     \(i : I) -> \(x : A) -> p x i
funext :: Term String
funext =
    lam "A" U (lam "B" U $
        let ab = "A" `arr` "B"
        in lam "f" ab $ lam "g" ab $
            let proofTy = pi "x" "A" $ path "B" ("f" :$ "x") ("g" :$ "x")
            in lam "p" proofTy $
                dlam "i" $ lam "x" "A" $
                    ("p" :$ "x") :@ "i"
    )
    `Ann` funextType

-- symA (x : A 0) (y : A 1) (p : PathD A x y) : PathD A y x =
--   <i> comp A 0 1 x [i=0 |> p, i=1 |> refl]
sym :: Scope () Type n -> Term n
sym a = Lam (instantiate1 I0 a) (hoas $ \x ->
            Lam (instantiate1 I1 (suc a)) $ hoas $ \y ->
                Lam (PathD (suc (suc a)) (suc x) y) $ hoas $ \p ->
                    DLam $ hoas $ \i ->
                        comp
                            (suc (suc (suc (suc a))))
                            I0
                            I1
                            (suc (suc (suc x)))
                            [
                                [i:=I0] :> hoas (suc (suc p) :@),
                                [i:=I1] :> lift (suc (suc (suc x)))
                                ]
    )
    `Ann`
    Pi (instantiate1 I0 a) (hoas $ \x ->
        Pi (instantiate1 I1 (suc a)) $ hoas $ \y ->
            Pi (PathD (suc (suc a)) (suc x) y)
                (lift $ PathD (suc (suc a)) y (suc x)))
