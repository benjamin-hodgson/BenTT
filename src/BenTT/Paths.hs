{-# LANGUAGE OverloadedStrings #-}
module BenTT.Paths (
    refl,
    comp,
    gcomp,
    ghcomp,
    funext,
    sym
) where

import Control.Monad.Trans (lift)
import Prelude hiding (pi)

import Bound (Scope, Var(B), instantiate1, toScope)
import Optics ((&), (%~))

import BenTT.DeBruijn (hoas, suc, unsafeClosed', deBruijn, suc2)
import BenTT.Syntax (
    Term(..),
    Face(..),
    Constraint(..),
    Type,
    System,
    arr,
    dlam,
    lam,
    path,
    pi
    )


refl :: Term n -> Term n
refl = DLam . lift


type Comp n = Comp' (Scope () Type) n
type HComp n = Comp' Type n
type Comp' ty n = ty n -> Term n -> Term n -> Term n -> System (Scope () Term) n -> Term n

comp :: Comp n
comp = doComp HComp

gcomp :: Comp n
gcomp = doComp ghcomp

doComp :: HComp n -> Comp n
doComp hcomp a r r' tm sys = hcomp
    (instantiate1 r' a)
    r
    r'
    (Coe a r r' tm)
    [cof :> n & deBruijn %~ Coe (suc a) (Var $ B ()) (suc r') | cof :> n <- sys]

ghcomp :: HComp n
ghcomp _ _ _ tm [] = tm
ghcomp a r r' tm sys@((s:=s':>n0) : rest) = HComp a r r' tm ([s:=I0 :> t I0 I1, s:=I1 :> t I1 I0] ++ sys)
    where
        t i0 i1 = toScope $
            HComp
                (suc a)
                (suc r)
                (Var $ B ())
                (suc tm)
                ([suc (s' := i0 :> n0), suc (s' := i1) :> hoas (\y -> ghcomp (suc2 a) (suc2 r) y (suc2 tm) (fmap suc2 rest))]
                    ++ fmap suc rest)


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
                                i := I0 :> hoas (suc (suc p) :@),
                                i := I1 :> lift (suc (suc (suc x)))
                                ]
    )
    `Ann`
    Pi (instantiate1 I0 a) (hoas $ \x ->
        Pi (instantiate1 I1 (suc a)) $ hoas $ \y ->
            Pi (PathD (suc (suc a)) (suc x) y)
                (lift $ PathD (suc (suc a)) y (suc x)))
