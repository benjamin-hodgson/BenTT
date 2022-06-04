{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.Except (lift)
import Prelude hiding (pi)

import BenTT.Eval (whnf)
import BenTT.Paths (sym)
import BenTT.PPrint (pprint)
import BenTT.Syntax (Term(..))
import BenTT.TypeCheck (infer)
import BenTT.Types (runTc)


main :: IO ()
main =
    case runTc (infer (sym (lift U))) (const undefined) whnf of
        Left err -> putStrLn $ "❌ " ++ err
        Right ok -> putStrLn $ "✅ " ++ pprint ok
