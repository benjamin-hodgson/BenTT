{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ViewPatterns #-}

module BenTT.TypeCheck (check, infer, assertEqual) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Data.Foldable (asum, for_, traverse_)
import Data.Traversable (for)
import Data.Functor
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Generics.Product (the)
import GHC.Generics

import Bound
import Optics hiding ((:>))

import BenTT.DeBruijn
import BenTT.Equiv
import BenTT.Paths
import BenTT.PPrint
import BenTT.Syntax
import BenTT.Types


check :: (Show n, Eq n) => Term n -> Type n -> Tc n ()
check x t = withError (++ "\nwhen checking " ++ pprint' x ++ " against " ++ pprint' t) (eval t >>= ck x)
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
    assert (#_Sig % _1) =<< eval =<< infer p
infer (Snd p) = do
    b <- assert (#_Sig % _2) =<< eval =<< infer p
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
assertEqual x y = join $ eq <$> eval x <*> eval y
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

        eq (Ann _ _) _ = error "shouldn't be possible after eval"
        eq _ (Ann _ _) = error "shouldn't be possible after eval"
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
