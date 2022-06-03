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
import BenTT.Eval
import BenTT.Paths
import BenTT.Types

main :: IO ()
main =
    case runTc (infer (sym (lift U))) (const undefined) whnf of
        Left err -> putStrLn $ "❌ " ++ err
        Right ok -> putStrLn $ "✅ " ++ pprint ok
