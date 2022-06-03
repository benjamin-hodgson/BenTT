{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ViewPatterns #-}

module BenTT.TypeCheck (check, infer, whnf) where

import Bound
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Optics hiding ((:>))
import Data.Foldable (asum, for_, traverse_)
import Data.Traversable (for)
import Data.Functor
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Generics.Product (the)
import GHC.Generics
import BenTT.DeBruijn
import BenTT.Syntax
import BenTT.PPrint
import BenTT.Equiv
import BenTT.Paths
import BenTT.Types


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
                (HComp a r r' (Fst x) [fs :> v & deBruijn %~ Fst | fs :> v <- sys])
                (comp
                    (hoas $ \j -> instantiate1 (HComp (suc a) (suc r) j (suc $ Fst x) [suc (fs :> v & deBruijn %~ Fst) | fs :> v <- sys]) (suc b))
                    r
                    r'
                    (Snd x)
                    [fs :> v & deBruijn %~ Snd | fs:>v <- sys]
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
        U -> return $ Glue x ([fs :> (instantiate1 r' b :* (coeEquiv b :@ r' :@ r)) | fs :> b <- sys] ++ [[r:=r'] :> x :* (idEquiv :$ x)])
        -- undefined: Glue
        _ -> asum [
            -- are we on a wall?
            asum [for_ fs (\(i:=j) -> assertEqual i j) *> whnf (instantiate1 r' c) | fs:>c <- sys],
            assertEqual r r' *> whnf x,  -- we're on a road to nowhere
            return h
            ]

whnf g@(Glue _ _) = return g
whnf g@(MkGlue _ _) = return g
whnf u@(Unglue g) =
    whnf g >>= \case
        MkGlue x _ -> whnf x
        _ -> return u

check :: (Show n, Eq n) => Term n -> Type n -> Tc n ()
check x t = withError (++ "\nwhen checking " ++ pprint' x ++ " against " ++ pprint' t) (whnf t >>= ck x)
    where
        ck Hole t = do
            throwError $ "Found hole with type " ++ pprint' t
        ck (Pair x y) (Sig a b) = do
            check x a
            check y (instantiate1 x b)
        ck (Lam d (fromScope -> b)) (Pi d' (fromScope -> r)) = do
            assertEqual d d'
            extend1 d' $ check b r
        ck (DLam b) (PathD (fromScope -> a) x y) = do
            extend1 I $ check (fromScope b) a
            withError (++ "\n when checking the start of a path") $
                assertEqual (instantiate1 I0 b) x
            withError (++ "\n when checking the end of a path") $
                assertEqual (instantiate1 I1 b) y
        ck (Let t x (fromScope -> b)) t1 = do
            check t U
            check x t
            extend1 t $ check b (suc t1)
        ck (MkGlue x sys) (Glue a sys') = undefined
        ck x t = do
            t1 <- infer x
            assertEqual t t1

infer :: (Show n, Eq n) => Term n -> Tc n (Type n)
infer Hole = throwError "can't infer hole"
infer U = return U  -- type in type
infer I = throwError "I is not kan"
infer I0 = return I
infer I1 = return I
infer (Var x) = lookupTy x
infer (Ann x t) = do
    check t U
    check x t
    return t
infer (f :$ x) = do
    (d, r) <- assert #_Pi =<< infer f
    check x d
    return $ instantiate1 x r
infer (Lam d (fromScope -> b)) = do
    check d U
    r <- extend1 d $ inferKan b
    return $ Pi d (toScope r)
infer (Pi d (fromScope -> r)) = do
    check d U
    extend1 d $ check r U
    return U
infer p@(Pair _ _) = throwError $ "Need a type annotation for pair: " ++ pprint' p
infer (Sig a (fromScope -> b)) = do
    check a U
    extend1 a $ check b U
    return U
infer (Fst p) =
    assert (#_Sig % _1) =<< whnf =<< infer p
infer (Snd p) = do
    b <- assert (#_Sig % _2) =<< whnf =<< infer p
    return $ instantiate1 (Fst p) b
infer (Let t x (fromScope -> b)) = do
    check t U
    check x t
    r <- extend1 t $ inferKan b
    return (instantiate1 x (toScope r))
infer (f :@ i) = do
    a <- assert (#_PathD % _1) =<< infer f
    check i I
    return $ instantiate1 i a
infer (DLam b) = do
    a <- extend1 I $ inferKan (fromScope b)
    return (PathD (toScope a) (instantiate1 I0 b) (instantiate1 I1 b))
infer (PathD ty x y) = do
    extend1 I $ check (fromScope ty) U
    check x (instantiate1 I0 ty)
    check y (instantiate1 I1 ty)
    return U
infer (Coe ty r r' x) = do
    extend1 I $ check (fromScope ty) U
    check r I
    check r' I
    check x (instantiate1 r ty)
    return $ instantiate1 r' ty
infer (HComp ty r r' x sys) = do
    check ty U
    check r I
    check r' I
    check x ty
    traverse_ checkTypes sys  -- the constraints should be well formed
    for_ sys $ \(fs:>y) -> do
        for_ (solveFaces fs) $ \subst -> do
            -- the faces should agree with y at the base
            withError (++ "\n when checking the base of the face " ++ foldMapOf (traversed % faceParts) pprint' fs) $ checkBase subst x y
            -- the faces should agree with each other (at all k) where they meet
            checkAdjacent subst y
    return ty

    where
        checkTypes (faces :> y) = do
            traverse_ (\(i:=j) -> check i I *> check j I) faces
            extend1 I $ check (fromScope y) (suc ty)

        solveFaces [] = Just emptySubst
        solveFaces ((Var i := j):fs) = composeFaceSubst i j fs
        solveFaces ((i := Var j):fs) = composeFaceSubst j i fs
        solveFaces ((i := j):fs)
            | i == j = solveFaces fs
            | otherwise = Nothing

        composeFaceSubst r r' fs = do
            let fs' = fs & traversed % faceParts %~ substitute r r'
            subst <- solveFaces fs'
            return $ addToSubst r r' subst

        checkBase subst x y = assertEqual (applySubst subst x) (applySubst subst $ instantiate1 r y)

        checkAdjacent subst y =
            let sys' = [fs & traversed % faceParts %~ applySubst subst :> z & deBruijn %~ applySubst (suc subst) | fs:>z <- sys]
            in for_ sys' $ \(fs:>z) ->
                for_ (solveFaces fs) $ \subst' ->
                    let [y', z'] = fmap (applySubst (suc subst') . fromScope) [y, z]
                    in extend1 I $ assertEqual y' z'

infer (Glue a sys) = do
    check a U
    for_ sys $ \(faces :> b :* e) -> do
        traverse_ (\(i:=j) -> check i I *> check j I) faces
        check b U
        check e (equiv :$ a :$ b)
        -- undefined: check that the constraints agree when they meet
    return U
infer (MkGlue x sys) = throwError "need type annotation for glue"
infer (Unglue x) = assert (#_Glue % _1) =<< infer x


assertEqual :: (Show n, Eq n) => Term n -> Term n -> Tc n ()
assertEqual x y = join $ eq <$> whnf x <*> whnf y
    where
        eq (f :$ x) (g :$ y)
            = assertEqual f g *> assertEqual x y

        eq (Lam t (fromScope -> b1)) (Lam _ (fromScope -> b2))
            = extend1 t $ assertEqual b1 b2  -- assume types equal
        -- eta
        eq (Lam t (fromScope -> b1)) y
            = extend1 t $ assertEqual b1 (suc y :$ Var (B ()))
        eq x (Lam t (fromScope -> b1))
            = extend1 t $ assertEqual (suc x :$ Var (B ())) b1

        eq (Pi d1 (fromScope -> r1)) (Pi d2 (fromScope -> r2)) = do
            assertEqual d1 d2
            extend1 d1 $ assertEqual r1 r2  -- d1 == d2 by now

        eq (Pair x1 y1) (Pair x2 y2) = do
            assertEqual x1 x2
            assertEqual y1 y2
        -- eta
        eq (Pair x y) p = do
            assertEqual x (Fst p)
            assertEqual y (Snd p)
        eq p (Pair x y) = do
            assertEqual (Fst p) x
            assertEqual (Snd p) y

        eq (Fst p1) (Fst p2) = assertEqual p1 p2
        eq (Snd p1) (Snd p2) = assertEqual p1 p2

        eq (Sig a1 (fromScope -> b1)) (Sig a2 (fromScope -> b2)) = do
            assertEqual a1 a2
            extend1 a1 $ assertEqual b1 b2

        eq (p :@ x) (q :@ y) = assertEqual p q *> assertEqual x y

        eq (DLam (fromScope -> b1)) (DLam (fromScope -> b2))
            = extend1 I $ assertEqual b1 b2
        -- eta
        eq (DLam (fromScope -> b1)) y
            = extend1 I $ assertEqual b1 (suc y :@ Var (B ()))
        eq x (DLam (fromScope -> b1))
            = extend1 I $ assertEqual (suc x :@ Var (B ())) b1

        eq (PathD (fromScope -> t1) x1 y1) (PathD (fromScope -> t2) x2 y2)
            = extend1 I (assertEqual t1 t2) *> assertEqual x1 x2 *> assertEqual y1 y2

        eq (Coe (fromScope -> t1) i1 j1 x1) (Coe (fromScope -> t2) i2 j2 x2) = do
            extend1 I (assertEqual t1 t2)
            assertEqual i1 i2
            assertEqual j1 j2
            assertEqual x1 x2

        eq (HComp a1 i1 j1 x1 sys1) (HComp a2 i2 j2 x2 sys2) = do
            assertEqual a1 a2
            assertEqual i1 i2
            assertEqual j1 j2
            assertEqual x1 x2
            eqSys sys1 sys2
        
        -- undefined: Glue, MkGlue, Unglue

        eq (Ann _ _) _ = error "shouldn't be possible after whnf"
        eq _ (Ann _ _) = error "shouldn't be possible after whnf"
        eq x y
            | x == y = return ()
            | otherwise = throwError $ "mismatched type: tried to compare\n  " ++ pprint' x ++ "\nto\n  " ++ pprint' y

        eqSys sys1 sys2 = undefined


assert :: Is k An_AffineFold => Optic' k is s a -> s -> Tc n a
assert l x = case x^?l of
    Just y -> return y
    Nothing -> throwError "mismatched type"


inferKan :: (Show n, Eq n) => Term n -> Tc n (Type n)
inferKan m = do
    t <- infer m
    if t == I
    then throwError "I is not kan"
    else return t


withError :: MonadError e m => (e -> e) -> m a -> m a
withError f m = catchError m (throwError . f)
