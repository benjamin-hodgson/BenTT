{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module BenTT.Eval (whnf) where

import Control.Monad.Trans (lift)

import Bound (fromScope, instantiate1, toScope)
import Optics ((&), (%~), (%), _2, each)

import BenTT.DeBruijn (deBruijn, hoas, suc, suc2, xchgScope)
import BenTT.Paths (comp)
import BenTT.Syntax (Term(..), Constraint(..), Face(..), System)
import BenTT.Types (Tc, extend1)
import BenTT.TypeCheck (infer)

whnf :: (Show n, Eq n) => Term n -> Tc n (Term n)
whnf Hole = return Hole
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
whnf c@(Coe (fromScope -> a) r r' x)
    | r == r' = whnf x  -- see "NOTE: equality of dimension terms"
    | otherwise = extend1 I (whnf a) >>= \case
        U -> whnf x
        Pi (toScope -> dom) range -> return $
            Lam (instantiate1 r' dom) $ hoas $ \arg ->
                Coe
                    -- `fmap suc range`, not `suc range`, because we want range's `B ()` to refer to `j`
                    (hoas $ \j -> instantiate1 (Coe (suc2 dom) j (suc2 r) (suc arg)) (fmap suc range))
                    (suc r)
                    (suc r')
                    (suc x :$ Coe (suc dom) (suc r') (suc r) arg)
        Sig (toScope -> a) b -> return $ Pair
            (Coe a r r' (Fst x))
            (Coe
                -- not suc-ing b inside this hoas because we want b's free variable to refer to j
                (hoas $ \j -> instantiate1 (Coe (suc a) (suc r) j (suc $ Fst x)) b)
                r
                r'
                (Snd x)
            )
        PathD ty m n -> return $
            DLam $ hoas $ \k ->
                comp
                    -- `ty` is a scope over `k` with a free variable `r`.
                    -- We want to compose in the `r` direction;
                    -- the newly free variable after xchg will refer to `k`
                    (xchgScope ty)
                    (suc r)
                    (suc r')
                    (suc x :@ k)
                    [
                        [k := I0] :> suc (toScope m),
                        [k := I1] :> suc (toScope n)
                    ]
        -- undefined: Box
        _ -> return c

whnf h@(HComp a r r' x sys)
    | r == r' = whnf x  -- see "NOTE: equality of dimension terms"
    | otherwise = whnf a >>= \case
        Pi dom range -> return $
            Lam dom $ hoas $ \arg ->
                HComp
                    (instantiate1 arg (suc range))
                    (suc r)
                    (suc r')
                    (suc x :$ arg)
                    (fmap suc sys & each % _2 % deBruijn %~ (:$ suc arg))
        Sig a b -> return $
            Pair
                (HComp a r r' (Fst x) (sys & each % _2 % deBruijn %~ Fst))
                (comp
                    (hoas $ \j -> instantiate1 (HComp (suc a) (suc r) j (suc $ Fst x) (map suc (sys & each % _2 % deBruijn %~ Fst))) (suc b))
                    r
                    r'
                    (Snd x)
                    (sys & each % _2 % deBruijn %~ Snd)
                )
        PathD ty m n -> return $
            DLam $ hoas $ \k ->
                let sys' = fmap suc sys ++ [[k:=I0] :> lift (suc m), [k:=I1] :> lift (suc n)]
                in HComp
                    (instantiate1 k (suc ty))
                    (suc r)
                    (suc r')
                    (suc x :@ k)
                    (sys' & each % _2 % deBruijn %~ (:@ suc k))
        U -> whnf $ Box r r' x sys
        -- undefined: Box
        _ -> case evalSys sys of
                (c:_) -> whnf (instantiate1 r' c)
                [] -> return h

whnf b@(Box r r' a sys)
    | r == r' = whnf a  -- see "NOTE: equality of dimension terms"
    | otherwise = case evalSys sys of
        (b:_) -> whnf (instantiate1 r' b)
        [] -> return b
whnf b@(MkBox x sys) =
    case evalSys sys of
        (y:_) -> whnf y
        _ -> return b
whnf u@(Unbox r r' b)
    | r == r' = whnf b  -- see "NOTE: equality of dimension terms"
    | otherwise = whnf b >>= \case
        MkBox x _ -> whnf x
        x -> infer b >>= \case
            Box r r' a sys -> case evalSys sys of
                (a:_) -> whnf $ Coe a r' r x  -- undefined: hmm
                [] -> return u
            _ -> return u


evalSys :: (Show n, Eq n) => System f n -> [f n]
evalSys sys = [x | cof:>x <- sys, all (\(i:=j) -> i==j) cof]  -- see "NOTE: equality of dimension terms"
