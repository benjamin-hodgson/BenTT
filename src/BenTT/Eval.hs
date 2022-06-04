{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module BenTT.Eval (whnf) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Foldable
import Data.Functor
import Data.Maybe

import Bound
import Optics hiding ((:>))

import BenTT.DeBruijn
import BenTT.Equiv
import BenTT.Paths
import BenTT.Syntax
import BenTT.Types
import BenTT.TypeCheck

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

-- gotta clean up these fillers
whnf c@(Coe (fromScope -> a) r r' x) =
    extend1 I (whnf a) >>= \case
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
        -- undefined: Glue
        _ -> (assertEqual r r' *> whnf x) <|> return c

whnf h@(HComp a r r' x sys) =
    whnf a >>= \case
        Pi dom range -> return $
            Lam dom $ hoas $ \arg ->
                let sys' = fmap suc sys
                in HComp
                    (instantiate1 arg (suc range))
                    (suc r)
                    (suc r')
                    (suc x :$ arg)
                    [f :> m & deBruijn %~ (:$ suc arg) | f :> m <- sys']
        Sig a b -> return $
            Pair
                (HComp a r r' (Fst x) [cof :> v & deBruijn %~ Fst | cof :> v <- sys])
                (comp
                    (hoas $ \j -> instantiate1 (HComp (suc a) (suc r) j (suc $ Fst x) [suc (cof :> v & deBruijn %~ Fst) | cof :> v <- sys]) (suc b))
                    r
                    r'
                    (Snd x)
                    [cof :> v & deBruijn %~ Snd | cof:>v <- sys]
                )
        PathD ty m n -> return $
            DLam $ hoas $ \k ->
                let sys' = fmap suc sys ++ [[k:=I0] :> lift (suc m), [k:=I1] :> lift (suc n)]
                in HComp
                    (instantiate1 k (suc ty))
                    (suc r)
                    (suc r')
                    (suc x :@ k)
                    [f :> y & deBruijn %~ (:@ suc k) | f :> y <- sys']
        U -> whnf $ Glue x ([cof :> (instantiate1 r' b :* (coeEquiv b :@ r' :@ r)) | cof :> b <- sys] ++ [[r:=r'] :> x :* (idEquiv :$ x)])
        -- undefined: Glue
        _ -> asum [
            -- are we on a wall?
            evalSys sys >>= \case
                [] -> empty
                (c:_) -> whnf (instantiate1 r' c),
            assertEqual r r' *> whnf x,  -- we're on a road to nowhere
            return h
            ]

whnf g@(Glue _ sys) =
    evalSys sys >>= \case
        ((b:*_):_) -> whnf b
        [] -> return g
whnf g@(MkGlue x sys) =
    evalSys sys >>= \case
        (y:_) -> whnf y
        _ -> return g
whnf u@(Unglue g) =
    whnf g >>= \case
        MkGlue x _ -> whnf x
        x -> infer g >>= \case
            Glue a sys -> evalSys sys >>= \case
                ((_ :* equiv):_) -> whnf $ Fst equiv :$ x
                _ -> return u
            _ -> return u


evalSys :: (Show n, Eq n) => System f n -> Tc n [f n]
evalSys sys = map (\(cof:>x) -> x) <$> filterM active sys
    where
        active (cof:>x) = assertOnCof cof $> True <|> pure False
        assertOnCof = traverse_ (\(i:=j) -> assertEqual i j)
