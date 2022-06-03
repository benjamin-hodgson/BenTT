{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module BenTT.Types (
    Ctx, Eval,
    Tc, runTc,
    withError,
    eval,
    lookupTy,
    extend,
    extend1
    ) where

import Control.Monad.Except
import Control.Monad.Reader

import Bound

import BenTT.Syntax
import BenTT.DeBruijn
import Control.Applicative


type Ctx n = n -> Type n
newtype Tc n a = Tc { unTc :: ReaderT (Ctx n, ReifiedEval) (Except String) a }
    deriving (Functor, Applicative, Monad, MonadError String, MonadPlus, Alternative)
type Eval = forall n. (Show n, Eq n) => Term n -> Tc n (Term n)

newtype ReifiedEval = ReifiedEval Eval

runTc :: Tc n a -> Ctx n -> Eval -> Either String a
runTc (Tc tc) ctx eval = runExcept $ runReaderT tc (ctx, ReifiedEval eval)

eval :: (Show n, Eq n) => Term n -> Tc n (Term n)
eval m = Tc (asks snd) >>= \(ReifiedEval f) -> f m

lookupTy :: n -> Tc n (Type n)
lookupTy n = Tc $ asks (\(ctx, _) -> ctx n)

extend :: (b -> Type n) -> Tc (Var b n) a -> Tc n a
extend t = Tc . withReaderT (\(ctx, eval) -> (cons t ctx, eval)) . unTc
    where
        cons t ctx (B b) = suc (t b)
        cons t ctx (F f) = suc (ctx f)

extend1 :: Type n -> Tc (Var b n) a -> Tc n a
extend1 = extend . const

withError :: MonadError e m => (e -> e) -> m a -> m a
withError f m = catchError m (throwError . f)
