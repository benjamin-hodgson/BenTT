{-# LANGUAGE OverloadedStrings #-}

module Main where

import Prelude hiding (pi)
import Bound
import Data.Void
import Control.Monad.Except
import Control.Monad.Reader
import BenTT.Syntax
import BenTT.PPrint
import BenTT.TypeCheck
import BenTT.Equiv
import BenTT.Paths

main :: IO ()
main =
    case runExcept $ runReaderT (infer (sym (lift U))) (const undefined) of
        Left err -> putStrLn $ "❌ " ++ err
        Right ok -> putStrLn $ "✅ " ++ pprint ok
