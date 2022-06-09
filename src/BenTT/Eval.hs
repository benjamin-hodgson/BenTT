{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module BenTT.Eval (whnf) where

import Control.Monad.Trans (lift)

import Bound (Var(..), fromScope, toScope, instantiate1, (>>>=))
import Optics ((&), (%~), (%), _2, each)

import BenTT.DeBruijn (deBruijn, hoas, suc, suc2, xchgScope, suc3)
import BenTT.Paths (comp, gcomp)
import BenTT.Syntax (Term(..), Constraint(..), Face(..), System)
import BenTT.Types (Tc, extend1)
import BenTT.TypeCheck (infer)

whnf :: (Show n, Eq n) => Term n -> Tc n (Term n)
whnf U = return U
whnf v@(Var _) = return v
whnf (Ann x _) = whnf x  -- discard annotations when evaluating
whnf a@(f :$ x) =
    whnf f >>= \case
        Lam _ b -> whnf (instantiate1 x b)
        _ -> return a
whnf l@(Lam _ _) = return l
whnf p@(Pi _ _) = return p
whnf p@(Pair _ _ ) = return p
whnf s@(Sig _ _) = return s
whnf m@(Fst p) =
    whnf p >>= \case
        Pair x _ -> whnf x
        _ -> return m
whnf m@(Snd p) =
    whnf p >>= \case
        Pair _ y -> whnf y
        _ -> return m
whnf (Let x _ b) = whnf $ instantiate1 x b
whnf I = return I
whnf I0 = return I0
whnf I1 = return I1
whnf a@(p :@ i) =
    whnf p >>= \case
        DLam b -> whnf $ instantiate1 i b
        _ -> do
            i' <- whnf i
            t <- infer p
            case (i', t) of
                (I0, PathD _ x _) -> whnf x
                (I1, PathD _ _ y) -> whnf y
                _ -> return a
whnf l@(DLam _) = return l
whnf p@(PathD {}) = return p

-- undefined: gotta clean up these fillers
whnf c@(Coe (fromScope -> a) r r' tm)
    | r == r' = whnf tm  -- see "NOTE: equality of dimension terms"
    | otherwise = extend1 I (whnf a) >>= \case
        U -> whnf tm
        Pi (toScope -> dom) range -> return $
            Lam (instantiate1 r' dom) $ hoas $ \arg ->
                Coe
                    -- `fmap suc range`, not `suc range`, because we want range's `B ()` to refer to `j`
                    (hoas $ \j -> instantiate1 (Coe (suc2 dom) j (suc2 r) (suc arg)) (fmap suc range))
                    (suc r)
                    (suc r')
                    (suc tm :$ Coe (suc dom) (suc r') (suc r) arg)
        Sig (toScope -> a) b -> return $ Pair
            (Coe a r r' (Fst tm))
            (Coe
                -- not suc-ing b inside this hoas because we want b's free variable to refer to j
                (hoas $ \j -> instantiate1 (Coe (suc a) (suc r) j (suc $ Fst tm)) b)
                r
                r'
                (Snd tm)
            )
        PathD ty p0 p1 -> return $
            DLam $ hoas $ \k ->
                comp
                    -- `ty` is a scope over `k` with a free variable `r`.
                    -- We want to compose in the `r` direction;
                    -- the newly free variable after xchg will refer to `k`
                    (xchgScope ty)
                    (suc r)
                    (suc r')
                    (suc tm :@ k)
                    [
                        k := I0 :> suc (toScope p0),
                        k := I1 :> suc (toScope p1)
                    ]
        -- undefined: this code is hideous
        Box s s' a sys -> whnf $
            let n b = let x = Var $ F (B ())
                          z = Var $ B ()
                      in Coe
                            (suc b)
                            (suc s')
                            (suc z)
                            (Coe (suc2 $ toScope $ instantiate1 s' b) (suc2 r) x (suc2 tm))
                o = toScope $
                    let z = Var $ B ()
                        body = HComp (suc a) (suc s') z (suc $ Unbox s s' (suc tm) sys) (fmap suc [cof :> toScope (Coe (suc b) z (suc s) (n b)) | cof:>b <- sys])
                    in body >>= \case
                        B () -> Var (B ())
                        F (B ()) -> suc r
                        F n -> Var n
                p = gcomp
                    (suc $ toScope a)
                    (suc r)
                    (suc r')
                    (suc $ instantiate1 (instantiate1 r (toScope s)) o)
                    ([cof :> toScope (n b >>= \case { B () -> suc s; F (B ()) -> Var (B ()); F n -> Var (F n) }) | cof:>b <- sys]
                        ++ [s := s' :> suc (toScope (Coe (suc $ toScope a) (suc r) (Var $ B ()) (suc tm)))])
                q b = gcomp
                    (suc $ b >>>= \case { B () -> r'; F n -> Var n})
                    (suc $ s >>= \case { B () -> r'; F n -> Var n})
                    (Var (B ()))
                    p
                    ([cof :> suc (toScope (n b >>= \case { B () -> Var (B ()); F (B ()) -> suc r'; F n -> Var n})) | cof:>b <- sys] ++ map suc [r := r' :> toScope (n b >>= \case { B () -> Var (B ()); F (B ()) -> suc r'; F n -> Var n})])
            in instantiate1 r' $ toScope $
                MkBox
                    (HComp a s s' p [cof :> toScope (Coe (suc b) (Var (B ())) (suc s') (suc $ q b)) | cof:>b <- sys])
                    [cof :> (q b >>= \case { B () -> s'; F n -> Var (F n)}) | cof:>b <- sys]
        _ -> return c

whnf h@(HComp a r r' tm sys)
    | r == r' = whnf tm  -- see "NOTE: equality of dimension terms"
    | otherwise = case evalSys sys of
        (c:_) -> whnf (instantiate1 r' c)
        [] -> whnf a >>= \case
            Pi dom range -> return $
                Lam dom $ hoas $ \arg ->
                    HComp
                        (instantiate1 arg (suc range))
                        (suc r)
                        (suc r')
                        (suc tm :$ arg)
                        (fmap suc sys & each % _2 % deBruijn %~ (:$ suc arg))
            Sig a b -> return $
                Pair
                    (HComp a r r' (Fst tm) (sys & each % _2 % deBruijn %~ Fst))
                    (comp
                        (hoas $ \j -> instantiate1 (HComp (suc a) (suc r) j (suc $ Fst tm) (map suc (sys & each % _2 % deBruijn %~ Fst))) (suc b))
                        r
                        r'
                        (Snd tm)
                        (sys & each % _2 % deBruijn %~ Snd)
                    )
            PathD ty p0 p1 -> return $
                DLam $ hoas $ \k ->
                    let sys' = fmap suc sys ++ [k := I0 :> lift (suc p0), k := I1 :> lift (suc p1)]
                    in HComp
                        (instantiate1 k (suc ty))
                        (suc r)
                        (suc r')
                        (suc tm :@ k)
                        (sys' & each % _2 % deBruijn %~ (:@ suc k))
            U -> whnf $ Box r r' tm sys
            -- undefined: this code is hideous
            Box s s' a sys' -> whnf $
                let unsafeUnsuc = fmap (\case { F f -> f; _ -> error "unsafeUnsuc" })
                    p b =
                        let z = Var (B ())
                        in HComp
                            (fromScope b)
                            (suc r)
                            (suc r')
                            (Coe (suc b) (suc s') z (suc tm))
                            [suc cof :> suc n & deBruijn %~ Coe (suc2 b) (suc2 s') (suc z) | cof:>n <- sys]
                    f c = hoas $ \z ->
                        HComp
                            (suc2 a)
                            (suc2 s')
                            z
                            (suc $ Unbox (suc s) (suc s') c (fmap suc sys'))
                            [suc2 cof :> hoas (\z' -> Coe (suc3 b) z' (suc3 s) (Coe (suc3 b) (suc3 s') z' (suc2 c))) | cof:>b <- sys']
                    o = HComp
                        a
                        r r'
                        (instantiate1 s (unsafeUnsuc (f (suc tm))))
                        [cof :> hoas (\y -> instantiate1 (suc s) (f n)) | cof:>(fromScope -> n) <- sys]
                    q = HComp
                        a
                        s
                        s'
                        o
                        ([cof :> unsafeUnsuc (f (suc $ instantiate1 r' n)) | cof:>n <- sys]
                            ++ [cof :> hoas (\z -> Coe (suc b) z (suc s) (p b)) | cof:>b <- sys']
                            ++ [r:=r' :> unsafeUnsuc (f (suc tm))])
                in MkBox q [cof :> instantiate1 s' (toScope (p b)) | cof:>b <- sys']
            _ -> return h

whnf b@(Box r r' a sys)
    | r == r' = whnf a  -- see "NOTE: equality of dimension terms"
    | otherwise = case evalSys sys of
        (b:_) -> whnf (instantiate1 r' b)
        [] -> return b
whnf b@(MkBox x sys) =
    case evalSys sys of
        (y:_) -> whnf y
        _ -> return b
whnf u@(Unbox r r' b sys)
    | r == r' = whnf b  -- see "NOTE: equality of dimension terms"
    | otherwise = whnf b >>= \case
        MkBox x _ -> whnf x
        x -> case evalSys sys of
            (a:_) -> whnf $ Coe a r' r x
            [] -> return u


evalSys :: (Show n, Eq n) => System f n -> [f n]
evalSys sys = [x | i:=j:>x <- sys, i==j]  -- see "NOTE: equality of dimension terms"
