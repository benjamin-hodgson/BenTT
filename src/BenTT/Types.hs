{-# LANGUAGE RankNTypes #-}

module BenTT.Types (
    Ctx,
    Tc,
    Eval,
    lookupTy,
    extend,
    extend1
    ) where

import Bound
import Control.Monad.Reader
import Control.Monad.Except
import BenTT.Syntax
import BenTT.DeBruijn

type Ctx n = n -> Type n
type Tc n = ReaderT (Ctx n) (Except String)
type Eval = forall n. Term n -> Tc n (Term n)

lookupTy :: n -> Tc n (Type n)
lookupTy n = asks ($ n)

extend :: (b -> Type n) -> Tc (Var b n) a -> Tc n a
extend t = withReaderT cons
    where
        cons ctx (B b) = suc (t b)
        cons ctx (F f) = suc $ ctx f

extend1 :: Type n -> Tc (Var b n) a -> Tc n a
extend1 = extend . const
