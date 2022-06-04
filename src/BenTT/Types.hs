{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module BenTT.Types (
    Ctx, Eval,
    Tc, runTc,
    eval,
    lookupTy,
    extend,
    extend1,
    withError
    ) where

import Bound (Var(..))

import BenTT.Syntax (Term, Type)
import BenTT.DeBruijn (suc)
import Control.Applicative (Alternative(..))
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad (MonadPlus(..), ap, liftM)


type Ctx n = n -> Type n
type Eval = forall n. (Show n, Eq n) => Term n -> Tc n (Term n)
newtype Tc n a = Tc { runTc :: Ctx n -> Eval -> Either String a }

instance Functor (Tc n) where
    fmap = liftM
instance Applicative (Tc n) where
    pure = return
    (<*>) = ap
instance Monad (Tc n) where
    return x = Tc $ \_ _ -> return x
    m >>= k = Tc $ \ctx eval -> do
        a <- runTc m ctx eval
        runTc (k a) ctx eval

instance MonadError String (Tc n) where
    throwError err = Tc $ \_ _ -> throwError err
    m `catchError` k = Tc $ \ctx eval ->
        case runTc m ctx eval of
            Right x -> Right x
            Left err -> runTc (k err) ctx eval

instance Alternative (Tc n) where
    empty = mzero
    (<|>) = mplus
instance MonadPlus (Tc n) where
    mzero = throwError ""
    m `mplus` g = m `catchError` const g

eval :: (Show n, Eq n) => Term n -> Tc n (Term n)
eval m = Tc (\ctx e -> runTc (e m) ctx e)

lookupTy :: n -> Tc n (Type n)
lookupTy n = Tc $ \ctx _ -> pure $ ctx n

extend :: (b -> Type n) -> Tc (Var b n) a -> Tc n a
extend t tc = Tc $ \ctx -> runTc tc (cons t ctx)
    where
        cons t ctx (B b) = suc (t b)
        cons t ctx (F f) = suc (ctx f)

extend1 :: Type n -> Tc (Var b n) a -> Tc n a
extend1 = extend . const

withError :: MonadError e m => (e -> e) -> m a -> m a
withError f m = catchError m (throwError . f)
