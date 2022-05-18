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

type Ctx n = n -> Type n
type Tc n = ReaderT (Ctx n) (Except String)

lookupTy :: n -> Tc n (Type n)
lookupTy n = asks ($ n)

extend :: Type n -> Tc (Var () n) a -> Tc n a
extend t = withReaderT cons
    where
        cons ctx (B ()) = suc t
        cons ctx (F f) = suc $ ctx f

whnf :: (Show n, Eq n) => Term n -> Tc n (Term n)
whnf Hole = throwError "can't evaluate hole"
whnf U = return U
whnf v@(Var _) = return v  -- free variables are stuck
whnf (Ann x _) = whnf x  -- discard annotations when evaluating
whnf a@(f :$ x) =
    asum [
        handleLam =<< assert #_Lam =<< whnf f,
        return a  -- stuck
        ]
    where
        handleLam (_, b) = whnf $ instantiate1 x b
whnf l@(Lam _ _) = return l
whnf p@(Pi _ _) = return p
whnf p@(Pair _ _ ) = return p
whnf s@(Sig _ _) = return s
whnf s@(Fst p) = asum [
        assert (#_Pair % _1) =<< whnf p,
        return s  -- stuck
    ]
whnf s@(Snd p) = asum [
        assert (#_Pair % _2) =<< whnf p,
        return s  -- stuck
    ]
whnf (Let x _ b) = whnf $ instantiate1 x b
whnf I = return I
whnf I0 = return I0
whnf I1 = return I1
whnf a@(p :@ i) = asum [
        -- if p is a dimension lambda, instantiate it with i and reduce.
        handleDLam =<< assert #_DLam =<< whnf p,
        -- if i is I0 or I1, extract the path endpoint
        tryGetEndpoint I0 _2,
        tryGetEndpoint I1 _3,
        -- otherwise, it's stuck
        return a
        ]
    where
        handleDLam b = whnf $ instantiate1 i b

        tryGetEndpoint expected getter = do
            assertEqual i expected
            ty <- infer p
            tup <- assert #_PathD ty
            whnf (tup^.getter)
whnf l@(DLam _) = return l
whnf p@(PathD {}) = return p
whnf c@(Coe (fromScope -> a) i j x) = do
    a' <- extend I (whnf a)
    asum [
        -- compute the coercion based on the type we're coercing in
        handlePi <$> assert #_Pi a',
        handlePathD <$> assert #_PathD a',
        handleU <$> assert #_U a',
        -- coe _ i i x = x
        handleNullCoercion,
        -- otherwise, it's stuck
        return c
        ]
    where
        handlePi (toScope -> d, r) =
            let argTy = instantiate1 j d
            in Lam argTy $ hoas $ \arg ->
                let coeArg = Coe (suc d) (suc j) (suc i) arg
                    returnTy = instantiate1 coeArg r
                in Coe (lift returnTy) (suc i) (suc j) (suc x :$ coeArg)

        handlePathD (ty, m, n) = DLam $ hoas $ \k ->
            comp ty (suc i) (suc j) (suc x :@ k) [
                [k := I0] :> suc (toScope m),
                [k := I1] :> suc (toScope n)]

        handleU _ = x

        handleNullCoercion = assertEqual i j $> x
whnf h@(HComp a i j x sys) = do
    a' <- whnf a
    asum [
        -- compute the composition based on the type we're composing in
        handlePi <$> assert #_Pi a',
        handlePathD <$> assert #_PathD a',
        handleU <$ assert #_U a',
        -- comp _ i i x _ = x
        handleNullComposition,
        -- one of the faces can be discharged
        handleMatchingPartialElement,
        -- otherwise, it's stuck
        return h
        ]
    where
        handlePi (d, r) = Lam d $ hoas $ \arg ->
            let sys' = fmap suc sys
            in HComp
                (instantiate1 arg (suc r))
                (suc i)
                (suc j)
                (suc x :$ arg)
                [f :> m & deBruijn %~ (:$ suc arg) | f :> m <- sys']

        handlePathD (ty, m, n) = DLam $ hoas $ \k ->
            let sys' = fmap suc sys ++ [[k:=I0] :> lift (suc m), [k:=I1] :> lift (suc n)]
            in HComp
                (instantiate1 k (suc ty))
                (suc i)
                (suc j)
                (suc x :@ k)
                [f :> y & deBruijn %~ (:@ suc k) | f :> y <- sys']

        handleU = Glue U []

        handleNullComposition = assertEqual i j $> x

        handleMatchingPartialElement =
            case [x | f:>x <- sys, all (\(i:=j) -> i == j) f] of
                [] -> throwError "no matching partial element"
                (x:_) -> whnf $ instantiate1 j x

whnf g@(Glue ty sys) = return g
whnf g@(MkGlue {}) = return g
whnf u@(Unglue g) = asum [
    assert (#_MkGlue % _3) g,
    return u
    ]

check :: (Show n, Eq n) => Term n -> Type n -> Tc n ()
check x t = ck x =<< whnf t
    where
        ck Hole t = do
            throwError $ "Found hole with type " ++ pprint' t
        ck (Pair x y) (Sig a b) = do
            check x a
            check y (instantiate1 x b)
        ck (Lam d (fromScope -> b)) (Pi d' (fromScope -> r)) = do
            assertEqual d d'
            extend d' $ check b r
        ck (DLam b) (PathD (fromScope -> a) x y) = do
            extend I $ check (fromScope b) a
            assertEqual (instantiate1 I0 b) x
            assertEqual (instantiate1 I1 b) y
        ck (Let t x (fromScope -> b)) t1 = do
            check t U
            check x t
            extend t $ check b (suc t1)
        ck x t = do
            t1 <- infer x
            catchError (assertEqual t t1) $ \e ->
                throwError $ e ++ "\nwhen checking\n  " ++ pprint' x ++ "\nagainst type\n " ++ pprint' t

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
    r <- extend d $ infer b
    return $ Pi d (toScope r)
infer (Pi d (fromScope -> r)) = do
    check d U
    extend d $ check r U
    return U
infer p@(Pair _ _) = throwError $ "Need a type annotation for pair: " ++ pprint' p
infer (Sig a (fromScope -> b)) = do
    check a U
    extend a $ check b U
    return U
infer (Fst p) = do
    (a, _) <- assert #_Sig =<< whnf =<< infer p
    return a
infer (Snd p) = do
    (_, b) <- assert #_Sig =<< whnf =<< infer p
    return $ instantiate1 (Fst p) b
infer (Let t x (fromScope -> b)) = do
    check t U
    check x t
    r <- extend t $ infer b
    return (instantiate1 x (toScope r))
infer (f :@ i) = do
    fty <- infer f
    case fty of
        PathD a _ _ -> do
            check i I
            return $ instantiate1 i a
        _ -> throwError "expected a path type"
infer (DLam b) = do
    a <- extend I $ infer (fromScope b)
    return (PathD (toScope a) (instantiate1 I0 b) (instantiate1 I1 b))
infer (PathD ty x y) = do
    extend I $ check (fromScope ty) U
    check x (instantiate1 I0 ty)
    check y (instantiate1 I1 ty)
    return U
infer (Coe ty i j x) = do
    extend I $ check (fromScope ty) U
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
            _ <- checkBase subst x y
            -- the faces should agree with each other (at all k) where they meet
            _ <- checkAdjacent subst y
            return ()
    return ty

    where
        checkTypes (faces :> y) = do
            traverse_ (\(i:=j) -> check i I >> check j I) faces
            extend I $ check (fromScope y) (suc ty)

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
                    in extend I $ assertEqual y' z'

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
infer (MkGlue a equivs x sys) = do
    let glue = Glue a equivs
    check glue U
    check x a
    undefined
    return glue
infer (Unglue x) = do
    (ty, sys) <- assert #_Glue =<< infer x
    return ty


assertEqual :: (Show n, Eq n) => Term n -> Term n -> Tc n ()
assertEqual x y | x == y = return ()  -- alpha equiv
                | otherwise = bind2 eq (whnf x) (whnf y)
    where
        eq (f :$ x) (g :$ y)
            = assertEqual f g >> assertEqual x y

        -- alpha equiv
        eq (Lam t (fromScope -> b1)) (Lam _ (fromScope -> b2))
            = extend t $ assertEqual b1 b2  -- assume types equal
        -- beta-eta equiv
        eq (Lam t (fromScope -> b1)) y
            = extend t $ assertEqual b1 (suc y :$ Var (B ()))
        eq x (Lam t (fromScope -> b1))
            = extend t $ assertEqual (suc x :$ Var (B ())) b1

        eq (Pi d1 (fromScope -> r1)) (Pi d2 (fromScope -> r2)) = do
            assertEqual d1 d2
            extend d1 $ assertEqual r1 r2  -- d1 == d2 by now

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
            extend a1 $ assertEqual b1 b2

        eq (f :@ x) (g :@ y) = assertEqual f g >> assertEqual x y

        -- alpha equiv
        eq (DLam (fromScope -> b1)) (DLam (fromScope -> b2))
            = extend I $ assertEqual b1 b2
        -- beta-eta equiv
        eq (DLam (fromScope -> b1)) y
            = extend I $ assertEqual b1 (suc y :@ Var (B ()))
        eq x (DLam (fromScope -> b1))
            = extend I $ assertEqual (suc x :@ Var (B ())) b1

        eq (PathD (fromScope -> t1) x1 y1) (PathD (fromScope -> t2) x2 y2)
            = extend I (assertEqual t1 t2) >> assertEqual x1 x2 >> assertEqual y1 y2

        eq (Coe (fromScope -> t1) i1 j1 x1) (Coe (fromScope -> t2) i2 j2 x2) = do
            extend I (assertEqual t1 t2)
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

assert :: Is k An_AffineFold => Optic' k is s a -> s -> Tc n a
assert l x = case x^?l of
    Just y -> return y
    Nothing -> throwError "mismatched type"

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 m x y = do
    x' <- x
    y' <- y
    m x' y'
