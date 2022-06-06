module BenTT.PPrint (pprint, pprint') where

import Control.Applicative (liftA2)
import Control.Monad.State (State, evalState, put, get)
import Data.List (intercalate)

import Bound (instantiate1)

import BenTT.Syntax (Term(..), Constraint(..), Face(..), System)


pprint' :: Show a => Term a -> String
pprint' = pprint . fmap show


pprint :: Term String -> String
pprint m = evalState (pp m) 0
    where
        pp Hole = return "_"
        pp U = return "U"
        pp (Var n) = return n
        pp (Ann tm ty) = do
            tm' <- pp tm
            ty' <- pp ty
            return $ tm' ++ " : " ++ ty'
        pp (f :$ x) = do
            f' <- pp f
            x' <- pp x
            return $ "(" ++ f' ++ ") (" ++ x' ++ ")"
        pp (Lam t b) = do
            var <- freshen "x"
            t' <- pp t
            let b' = instantiate1 (Var var) b
            b'' <- pp b'
            return $ "\\(" ++ discard var b' ++ " : " ++ t' ++ ") -> " ++ b''
        pp (Pi d r) = do
            var <- freshen "x"
            d' <- pp d
            let r' = instantiate1 (Var var) r
            r'' <- pp r'
            return $ if var `elem` r'
                then "(" ++ var ++ " : " ++ d' ++ ") -> " ++ r''
                else "(" ++ d' ++ " -> " ++ r'' ++ ")"
        pp (Sig a b) = do
            var <- freshen "x"
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
            var <- freshen "x"
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
            var <- freshen "i"
            let b' = instantiate1 (Var var) b
            b'' <- pp b'
            return $ "<" ++ discard var b' ++ "> " ++ b''
        pp (PathD ty x y) = do
            var <- freshen "i"
            let ty' = instantiate1 (Var var) ty
            ty'' <- pp ty'
            x' <- pp x
            y' <- pp y
            return $ "PathD (" ++ discard var ty' ++ ". " ++ ty'' ++ ") (" ++ x' ++ ") (" ++ y' ++ ")"
        pp (Coe ty r s x) = do
            var <- freshen "i"
            let ty' = instantiate1 (Var var) ty
            ty'' <- pp ty'
            r' <- pp r
            s' <- pp s
            x' <- pp x
            return $ "coe (" ++ ty'' ++ ") (" ++ r' ++ "->" ++ s' ++ ") (" ++ x' ++ ")"
        pp (HComp ty r s x sys) = do
            var <- freshen "i"
            ty' <- pp ty
            r' <- pp r
            s' <- pp s
            x' <- pp x
            sys' <- ppSys sys $ \m -> do
                let m' = instantiate1 (Var var) m
                m'' <- pp m'
                return $ discard var m' ++ ". " ++ m''
            return $ "hcomp (" ++ ty' ++ ") (" ++ r' ++ "->" ++ s' ++ ") (" ++ x' ++ ") [" ++ sys' ++ "]"
        pp (Box r s ty sys) = pp $ HComp U r s ty sys
        pp (MkBox x sys) = do
            x' <- pp x
            sys' <- ppSys sys pp
            return $ "box " ++ x' ++ " [" ++ sys' ++ "]"
        pp (Unbox r s x sys) = do
            var <- freshen "i"
            r' <- pp r
            s' <- pp s
            x' <- pp x
            sys' <- ppSys sys $ \m -> do
                let m' = instantiate1 (Var var) m
                m'' <- pp m'
                return $ discard var m' ++ ". " ++ m''
            return $ "Unbox (" ++ r' ++ "<-" ++ s' ++ ") (" ++ x' ++ ") [" ++ sys' ++ "]"

        ppSys :: System f String -> (f String -> State Int String) -> State Int String
        ppSys sys f = intercalate ", " <$> traverse (ppConstr f) sys

        ppConstr f (cof :> x) = do
            cof' <- unwords <$> traverse ppFace cof
            x' <- f x
            return $ cof' ++ " |> " ++ x'

        ppFace :: Face String -> State Int String
        ppFace (i:=j) = liftA2 (\i' j' -> i' ++ "=" ++ j') (pp i) (pp j)

freshen :: String -> State Int String
freshen hint = do
    c <- get
    let v = hint ++ show c
    put (c+1)
    return v

discard :: String -> Term String -> String
discard x t | x `elem` t = x
            | otherwise = "_"

