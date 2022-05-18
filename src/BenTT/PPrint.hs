module BenTT.PPrint (pprint, pprint') where

import Bound
import Control.Monad.State
import BenTT.Syntax
import Data.List (intercalate)
import Control.Applicative
import Data.Traversable


pprint' :: Show a => Term a -> String
pprint' = pprint . fmap show


pprint :: Term String -> String
pprint x = evalState (pp x) 0
    where
        pp U = return "U"
        pp (Var v) = return v
        pp (Ann tm ty) = do
            tm' <- pp tm
            ty' <- pp ty
            return $ tm' ++ " : " ++ ty'
        pp (f :$ x) = do
            f' <- pp f
            x' <- pp x
            return $ "(" ++ f' ++ ") (" ++ x' ++ ")"
        pp (Lam t b) = do
            var <- fresh "x"
            t' <- pp t
            let b' = instantiate1 (Var var) b
            b'' <- pp b'
            return $ "\\(" ++ discard var b' ++ " : " ++ t' ++ ") -> " ++ b''
        pp (Pi d r) = do
            var <- fresh "x"
            d' <- pp d
            let r' = instantiate1 (Var var) r
            r'' <- pp r'
            return $ if var `elem` r'
                then "(" ++ var ++ " : " ++ d' ++ ") -> " ++ r''
                else "(" ++ d' ++ " -> " ++ r'' ++ ")"
        pp (Sig a b) = do
            var <- fresh "x"
            a' <- pp a
            let b' = instantiate1 (Var var) b
            b'' <- pp b'
            return $ if var `elem` b'
                then "Sig (" ++ var ++ " : " ++ a' ++ ") " ++ b''
                else "Sig (" ++ a' ++ ") (" ++ b'' ++ ")"
        pp (Pair x y) = liftA2 (\x' y' -> "(" ++ x' ++ ", " ++ y' ++ ")") (pp x) (pp y)
        pp (Fst p) = fmap (\p' -> "fst (" ++ p' ++ ")") (pp p)
        pp (Snd p) = fmap (\p' -> "snd (" ++ p' ++ ")") (pp p)
        pp (Let x t b) = do
            x' <- pp x
            t' <- pp t
            var <- fresh "x"
            let b' = instantiate1 (Var var) b
            b'' <- pp b'
            return $ "let " ++ var ++ " : " ++ t' ++ " = " ++ x' ++ " in " ++ b''
        pp I = return "I"
        pp I0 = return "I0"
        pp I1 = return "I1"
        pp (f :@ x) = do
            f' <- pp f
            x' <- pp x
            return $ "(" ++ f' ++ ") @ (" ++ x' ++ ")"
        pp (DLam b) = do
            var <- fresh "i"
            let b' = instantiate1 (Var var) b
            b'' <- pp b'
            return $ "<" ++ discard var b' ++ "> " ++ b''
        pp (PathD ty x y) = do
            var <- fresh "i"
            let ty' = instantiate1 (Var var) ty
            ty'' <- pp ty'
            x' <- pp x
            y' <- pp y
            return $ "PathD (" ++ discard var ty' ++ ". " ++ ty'' ++ ") (" ++ x' ++ ") (" ++ y' ++ ")"
        pp (Coe ty i j x) = do
            var <- fresh "i"
            let ty' = instantiate1 (Var var) ty
            ty'' <- pp ty'
            i' <- pp i
            j' <- pp j
            x' <- pp x
            return $ "coe (" ++ ty'' ++ ") (" ++ i' ++ "->" ++ j' ++ ") (" ++ x' ++ ")"
        pp (HComp ty i j x sys) = do
            var <- fresh "i"
            ty' <- pp ty
            i' <- pp i
            j' <- pp j
            x' <- pp x
            sys' <- ppSys sys $ \m -> do
                let m' = instantiate1 (Var var) m
                m'' <- pp m'
                return $ discard var m' ++ ". " ++ m''
            return $ "hcomp (" ++ ty' ++ ") (" ++ i' ++ "->" ++ j' ++ ") (" ++ x' ++ ") [" ++ sys' ++ "]"
        pp (Glue ty sys) = do
            ty' <- pp ty
            sys' <- ppSys sys $ \(t :* e) -> do
                t' <- pp t
                e' <- pp e
                return $ "(" ++ t' ++ ", " ++ e' ++ ")"
            return $ "Glue " ++ ty' ++ " [" ++ sys' ++ "]"
        pp (MkGlue a sys x sys1) = do
            glue <- pp (Glue a sys)
            x' <- pp x
            sys' <- ppSys sys1 pp
            return $ "glue {" ++ glue ++ "} " ++ x' ++ " [" ++ sys' ++ "]"
        pp (Unglue x) = fmap ("unglue " ++) (pp x)


        ppSys :: System f String -> (f String -> State Int String) -> State Int String
        ppSys sys f = intercalate ", " <$> traverse (ppConstr f) sys

        ppConstr f (faces :> x) = do
            faces' <- unwords <$> traverse ppFace faces
            x' <- f x
            return $ faces' ++ " |> " ++ x'

        ppFace (i:=j) = liftA2 (\i' j' -> i' ++ "=" ++ j') (pp i) (pp j)

fresh :: String -> State Int String
fresh hint = do
    c <- get
    let v = hint ++ show c
    put (c+1)
    return v

discard :: String -> Term String -> String
discard x t | x `elem` t = x
            | otherwise = "_"

