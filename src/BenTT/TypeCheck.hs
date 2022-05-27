{-# LANGUAGE FlexibleContexts #-}
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

type Ctx n = n -> Type n
type Tc n = ReaderT (Ctx n) (Except String)

lookupTy :: n -> Tc n (Type n)
lookupTy n = asks ($ n)

extend :: (b -> Type n) -> Tc (Var b n) a -> Tc n a
extend t = withReaderT cons
    where
        cons ctx (B b) = suc (t b)
        cons ctx (F f) = suc $ ctx f

extend1 :: Type n -> Tc (Var b n) a -> Tc n a
extend1 = extend . const

whnf :: (Show n, Eq n) => Term n -> Term n
whnf Hole = Hole
whnf U = U
whnf v@(Var _) = v  -- free variables are stuck
whnf (Ann x _) = whnf x  -- discard annotations when evaluating
whnf ((whnf -> Lam t b) :$ x) = whnf $ instantiate1 x b
whnf a@(_ :$ _) = a  -- stuck
whnf l@(Lam _ _) = l
whnf p@(Pi _ _) = p
whnf p@(Pair _ _ ) = p
whnf s@(Sig _ _) = s
whnf (Fst (whnf -> Pair x _)) = whnf x
whnf m@(Fst _) = m  -- stuck
whnf (Snd (whnf -> Pair _ y)) = whnf y
whnf m@(Snd _) = m  -- stuck
whnf (Let x _ b) = whnf $ instantiate1 x b
whnf I = I
whnf I0 = I0
whnf I1 = I1
whnf ((whnf -> DLam b) :@ i) = whnf $ instantiate1 i b
whnf a@(_ :@ _) = a
whnf l@(DLam _) = l
whnf p@(PathD {}) = p
whnf (Coe (whnf . fromScope -> U) i j x) = x
whnf (Coe (whnf . fromScope -> Pi (toScope -> d) r) i j x) =
    let argTy = instantiate1 j d
    in Lam argTy $ hoas $ \arg ->
        let coeArg = Coe (suc d) (suc j) (suc i) arg
            returnTy = instantiate1 coeArg r
        in Coe (lift returnTy) (suc i) (suc j) (suc x :$ coeArg)
whnf (Coe (whnf . fromScope -> PathD ty m n) i j x) =
    DLam $ hoas $ \k ->
        comp ty (suc i) (suc j) (suc x :@ k) [
            [k := I0] :> suc (toScope m),
            [k := I1] :> suc (toScope n)]
whnf c@(Coe a i j x)
    -- undefined: nf i == nf j
    | whnf i == whnf j = x
    | otherwise = c
-- whnf (HComp (whnf -> U) i j x sys) = undefined
whnf (HComp (whnf -> Pi d r) i j x sys) =
    Lam d $ hoas $ \arg ->
        let sys' = fmap suc sys
        in HComp
            (instantiate1 arg (suc r))
            (suc i)
            (suc j)
            (suc x :$ arg)
            [f :> m & deBruijn %~ (:$ suc arg) | f :> m <- sys']
whnf (HComp (whnf -> PathD ty m n) i j x sys) =
    DLam $ hoas $ \k ->
        let sys' = fmap suc sys ++ [[k:=I0] :> lift (suc m), [k:=I1] :> lift (suc n)]
        in HComp
            (instantiate1 k (suc ty))
            (suc i)
            (suc j)
            (suc x :@ k)
            [f :> y & deBruijn %~ (:@ suc k) | f :> y <- sys']
whnf h@(HComp a i j x sys) =
    -- undefined: nf i == nf j
    case [x | f:>x <- sys, all (\(i':=j') -> whnf i' == whnf j') f] of
        -- we're on one of the tubes
        (x:_) -> whnf $ instantiate1 j x
        [] | whnf i == whnf j -> x
           | otherwise -> h
whnf g@(Glue _ _) = g
whnf g@(MkGlue _ _) = g
whnf (Unglue (whnf -> MkGlue x _)) = x
whnf u@(Unglue _) = u

check :: (Show n, Eq n) => Term n -> Type n -> Tc n ()
check x t = withError (++ "\nwhen checking " ++ pprint' x ++ " against " ++ pprint' t) $ ck x (whnf t)
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
        ck x t = do
            t1 <- infer x
            assertEqual t t1

infer :: (Show n, Eq n) => Term n -> Tc n (Type n)
infer Hole = throwError "can't infer hole"
infer U = return U  -- type in type
infer I = throwError "I is not a type"
infer I0 = return I
infer I1 = return I
infer (Var x) = lookupTy x
infer (Ann x t) = do
    check t U
    check x t
    return t
infer (f :$ x) = do
    fty <- infer f
    case fty of
        Pi d r -> do
            xSys <- check x d
            return $ instantiate1 x r
        _ -> throwError "expected a function type"
infer (Lam d (fromScope -> b)) = do
    check d U
    r <- extend1 d $ infer b
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
infer (Fst p) = do
    (a, _) <- assert #_Sig . whnf =<< infer p
    return a
infer (Snd p) = do
    (_, b) <- assert #_Sig . whnf =<< infer p
    return $ instantiate1 (Fst p) b
infer (Let t x (fromScope -> b)) = do
    check t U
    check x t
    r <- extend1 t $ infer b
    return (instantiate1 x (toScope r))
infer (f :@ i) = do
    fty <- infer f
    case fty of
        PathD a _ _ -> do
            check i I
            return $ instantiate1 i a
        _ -> throwError "expected a path type"
infer (DLam b) = do
    a <- extend1 I $ infer (fromScope b)
    return (PathD (toScope a) (instantiate1 I0 b) (instantiate1 I1 b))
infer (PathD ty x y) = do
    extend1 I $ check (fromScope ty) U
    check x (instantiate1 I0 ty)
    check y (instantiate1 I1 ty)
    return U
infer (Coe ty i j x) = do
    extend1 I $ check (fromScope ty) U
    check i I
    check j I
    check x (instantiate1 i ty)
    return $ instantiate1 j ty
infer (HComp ty i j x sys) = do
    check ty U
    check i I
    check j I
    check x ty
    traverse_ checkTypes sys  -- the constraints should be well formed
    for_ sys $ \(fs:>y) -> do
        for_ (solveFaces fs) $ \subst -> do
            -- the faces should agree with y at the base
            withError (++ "\n when checking the base of the face " ++ foldMapOf (traversed % faceParts) pprint' fs) $ checkBase subst x y
            -- the faces should agree with each other (at all k) where they meet
            checkAdjacent subst y
            return ()
    return ty

    where
        checkTypes (faces :> y) = do
            traverse_ (\(i:=j) -> check i I >> check j I) faces
            extend1 I $ check (fromScope y) (suc ty)

        solveFaces [] = Just emptySubst
        solveFaces ((Var i := j):fs) = composeFaceSubst i j fs
        solveFaces ((i := Var j):fs) = composeFaceSubst j i fs
        solveFaces ((i := j):fs)
            | i == j = solveFaces fs
            | otherwise = Nothing

        composeFaceSubst i j fs = do
            let fs' = fs & traversed % faceParts %~ substitute i j
            subst <- solveFaces fs'
            return $ addToSubst i j subst

        checkBase subst x y = assertEqual (applySubst subst x) (applySubst subst $ instantiate1 i y)

        checkAdjacent subst y =
            let sys' = [fs & traversed % faceParts %~ applySubst subst :> z & deBruijn %~ applySubst (suc subst) | fs:>z <- sys]
            in for_ sys' $ \(fs:>z) ->
                for_ (solveFaces fs) $ \subst' ->
                    let [y', z'] = fmap (applySubst (suc subst') . fromScope) [y, z]
                    in extend1 I $ assertEqual y' z'

infer (Glue a sys) = do
    check a U
    for_ sys $ \(faces :> b :* e) -> do
        traverse_ (\(i:=j) -> check i I >> check j I) faces
        check b U
        -- check that e is an equivalence between a and b
        undefined
        -- check that the constraints agree when they meet
        undefined
    return U
infer (MkGlue x sys) = throwError "need type annotation for glue"
infer (Unglue x) = do
    (ty, sys) <- assert #_Glue =<< infer x
    return ty


assertEqual :: (Show n, Eq n) => Term n -> Term n -> Tc n ()
assertEqual x y | x == y = return ()  -- alpha equiv
                | otherwise = eq (whnf x) (whnf y)
    where
        eq (f :$ x) (g :$ y)
            = assertEqual f g >> assertEqual x y

        -- alpha equiv
        eq (Lam t (fromScope -> b1)) (Lam _ (fromScope -> b2))
            = extend1 t $ assertEqual b1 b2  -- assume types equal
        -- beta-eta equiv
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
        -- eta equiv
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

        eq (p :@ (whnf -> I0)) y = endpoint p _2 >>= assertEqual y
        eq (p :@ (whnf -> I1)) y = endpoint p _3 >>= assertEqual y
        eq x (q :@ (whnf -> I0)) = endpoint q _2 >>= assertEqual x
        eq x (q :@ (whnf -> I1)) = endpoint q _3 >>= assertEqual x
        eq (p :@ x) (q :@ y) = assertEqual p q >> assertEqual x y

        -- alpha equiv
        eq (DLam (fromScope -> b1)) (DLam (fromScope -> b2))
            = extend1 I $ assertEqual b1 b2
        -- beta-eta equiv
        eq (DLam (fromScope -> b1)) y
            = extend1 I $ assertEqual b1 (suc y :@ Var (B ()))
        eq x (DLam (fromScope -> b1))
            = extend1 I $ assertEqual (suc x :@ Var (B ())) b1

        eq (PathD (fromScope -> t1) x1 y1) (PathD (fromScope -> t2) x2 y2)
            = extend1 I (assertEqual t1 t2) >> assertEqual x1 x2 >> assertEqual y1 y2

        eq (Coe (fromScope -> t1) i1 j1 x1) (Coe (fromScope -> t2) i2 j2 x2) = do
            extend1 I (assertEqual t1 t2)
            assertEqual i1 i2
            assertEqual j1 j2
            assertEqual x1 x2
        -- coe _ i i x = x
        eq (Coe t i j x) y = do
            assertEqual i j
            assertEqual x y
        eq x (Coe t i j y) = do
            assertEqual i j
            assertEqual x y

        -- eq hcomp

        eq (Ann _ _) _ = error "shouldn't be possible after whnf"
        eq _ (Ann _ _) = error "shouldn't be possible after whnf"
        eq x y
            | x == y = return ()
            | otherwise = throwError $ "mismatched type: tried to compare\n  " ++ pprint' x ++ "\nto\n  " ++ pprint' y

        endpoint p getter =
            fmap (\tup -> whnf (tup^.getter)) $ assert #_PathD =<< infer p

assert :: Is k An_AffineFold => Optic' k is s a -> s -> Tc n a
assert l x = case x^?l of
    Just y -> return y
    Nothing -> throwError "mismatched type"

withError :: MonadError e m => (e -> e) -> m a -> m a
withError f m = catchError m (throwError . f)
