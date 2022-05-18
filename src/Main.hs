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

-- funext : (A B : U) (f g : A -> B)
--   ((x : A) -> Path B (f x) (g x))
--   -> Path (A -> B) f g
funextType :: Type String
funextType = pi "A" U $ pi "B" U $
    let ab = "A" `arr` "B"
    in pi "f" ab $ pi "g" ab $
        let proofTy = pi "x" "A" $ path "B" ("f" :$ "x") ("g" :$ "x")
        in proofTy `arr` path ab "f" "g"

-- funext = \(A B : U)
--     \(f g : A -> B)
--     \(p : (x : A) -> Path B (f x) (g x))
--     \(i : I) -> \(x : A) -> p x i
funext :: Term String
funext =
    lam "A" U (lam "B" U $
        let ab = "A" `arr` "B"
        in lam "f" ab $ lam "g" ab $
            let proofTy = pi "x" "A" $ path "B" ("f" :$ "x") ("g" :$ "x")
            in lam "p" proofTy $
                dlam "i" $ lam "x" "A" $
                    ("p" :$ "x") :@ "i")
    `Ann` funextType

main :: IO ()
main =
    case runExcept $ runReaderT (infer (pathToEquiv :$ U :$ U :$ refl U)) (const undefined) of
        Left err -> putStrLn $ "❌ " ++ err
        Right ok -> putStrLn $ "✅ " ++ pprint ok
