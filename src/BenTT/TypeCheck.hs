{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ViewPatterns #-}

module BenTT.TypeCheck (check, infer, assertEqual, assert) where

import Control.Monad.Except ( join, throwError )
import Data.Foldable (asum, for_, traverse_)
import Data.Traversable (for)
import Data.Maybe (fromJust)

import Bound (Var(..), fromScope, instantiate1, toScope, substitute )
import Optics (
    Optic',
    Is,
    An_AffineFold,
    foldMapOf,
    traversed,
    _1,
    _2,
    (&),
    (%),
    (%~),
    (^?)
    )

import BenTT.DeBruijn (Subst, addToSubst, applySubst, emptySubst, suc, deBruijn)
import BenTT.Equiv (equiv)
import BenTT.PPrint (pprint')
import BenTT.Syntax (
    Term(..),
    Constraint(..),
    Face(..),
    (:*)(..),
    System,
    Type,
    faceParts
    )
import BenTT.Types (Tc, extend1, lookupTy, eval, withError)


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
        ck (MkBox x sys) (Box r r' ty sys') = do
            check x ty
            -- undefined: check that the sys cofibration agrees with the sys' one
            for_ sys $ \(cof:>y) -> do
                for (findAdjacent cof sys') $ \(subst, t) -> do
                    check y (instantiate1 r' t)
                    assertEqual (Coe t r r' x) y
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
    for_ sys $ \(cof:>y) ->
        for_ (solve cof) $ \subst -> do
            -- the faces should agree with y at the base
            withError (++ "\n when checking the base of the face " ++ foldMapOf (traversed % faceParts) pprint' cof) $ checkBase subst x y
            -- the faces should agree with each other (at all k) where they meet
            checkAdjacent subst y
    return ty

    where
        checkTypes (cof:>y) = do
            traverse_ (\(i:=j) -> check i I *> check j I) cof
            extend1 I $ check (fromScope y) (suc ty)

        solve [] = Just emptySubst
        solve ((Var i := j):cof) = composeFaceSubst i j cof
        solve ((i := Var j):cof) = composeFaceSubst j i cof
        solve ((i := j):cof)
            | i == j = solve cof  -- undefined: assertEqual, not ==?
            | otherwise = Nothing

        composeFaceSubst r r' cof = do
            let cof' = cof & traversed % faceParts %~ substitute r r'
            subst <- solve cof'
            return $ addToSubst r r' subst

        checkBase subst x y = assertEqual (applySubst subst x) (applySubst subst $ instantiate1 r y)

        checkAdjacent subst y =
            let sys' = [cof & traversed % faceParts %~ applySubst subst :> z & deBruijn %~ applySubst (suc subst) | cof:>z <- sys]
            in for_ sys' $ \(cof:>z) ->
                for_ (solve cof) $ \subst' ->
                    let [y', z'] = fmap (applySubst (suc subst') . fromScope) [y, z]
                    in extend1 I $ assertEqual y' z'

infer (Box r r' ty sys) = do
    check ty U
    for_ sys $ \(cof :> (fromScope -> b)) -> do
        traverse_ (\(i:=j) -> check i I *> check j I) cof
        extend1 I $ check b U
        -- undefined: check that the constraints agree when they meet
    return U
infer (MkBox x sys) = throwError "need type annotation for box"
infer (Unbox r r' x) = assert (#_Box % _1) =<< infer x


assertEqual :: (Show n, Eq n) => Term n -> Term n -> Tc n ()
assertEqual x y = join $ eq <$> eval x <*> eval y
    where
        eq (f :$ x) (g :$ y) = do
            assertEqual f g
            assertEqual x y

        eq (Lam t (fromScope -> b1)) (Lam _ (fromScope -> b2))
            = extend1 t $ assertEqual b1 b2  -- assume types equal
        eq (Lam t (fromScope -> b)) f = etaLam t b f
        eq f (Lam t (fromScope -> b)) = etaLam t b f

        eq (Pi d1 (fromScope -> r1)) (Pi d2 (fromScope -> r2)) = do
            assertEqual d1 d2
            extend1 d1 $ assertEqual r1 r2

        eq (Pair x1 y1) (Pair x2 y2) = do
            assertEqual x1 x2
            assertEqual y1 y2
        eq (Pair x y) p = etaPair x y p
        eq p (Pair x y) = etaPair x y p

        eq (Fst p1) (Fst p2) = assertEqual p1 p2
        eq (Snd p1) (Snd p2) = assertEqual p1 p2

        eq (Sig a1 (fromScope -> b1)) (Sig a2 (fromScope -> b2)) = do
            assertEqual a1 a2
            extend1 a1 $ assertEqual b1 b2

        eq (p :@ x) (q :@ y) = do
            assertEqual p q
            assertEqual x y

        eq (DLam (fromScope -> b1)) (DLam (fromScope -> b2))
            = extend1 I $ assertEqual b1 b2
        eq (DLam (fromScope -> b)) p = etaDLam b p
        eq p (DLam (fromScope -> b)) = etaDLam b p

        eq (PathD (fromScope -> t1) x1 y1) (PathD (fromScope -> t2) x2 y2) = do
            extend1 I (assertEqual t1 t2)
            assertEqual x1 x2
            assertEqual y1 y2

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
        
        eq (Box r1 s1 a1 sys1) (Box r2 s2 a2 sys2) = do
            assertEqual r1 r2
            assertEqual s1 s2
            assertEqual a1 a2
            eqSys sys1 sys2

        eq (MkBox x1 sys1) (MkBox x2 sys2) = do
            assertEqual x1 x2
            eqSys sys1 sys2
        -- undefined: eta

        eq (Unbox r1 s1 g1) (Unbox r2 s2 g2) = do
            assertEqual r1 r2
            assertEqual s1 s2
            assertEqual g1 g2

        eq (Ann _ _) _ = error "eval should discard annotations"
        eq _ (Ann _ _) = error "eval should discard annotations"
        eq x y
            | x == y = return ()
            | otherwise = throwError $ "mismatched type: tried to compare\n  " ++ pprint' x ++ "\nto\n  " ++ pprint' y

        etaLam t b f = extend1 t $ assertEqual b (suc f :$ Var (B ()))
        etaDLam b p = extend1 I $ assertEqual b (suc p :@ Var (B ()))
        etaPair x y p = do
            assertEqual x (Fst p)
            assertEqual y (Snd p)
        
        eqSys sys1 sys2 = undefined


findAdjacent :: [Face n] -> System f n -> [(Subst Term n, f n)]
findAdjacent fs sys = undefined


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
