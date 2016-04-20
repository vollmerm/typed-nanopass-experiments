{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE DataKinds       #-}

module Language.Nanopass where

import Data.Constraint


-------------------------------------------------------------------------
-- GADT approach #1
-------------------------------------------------------------------------

-- Collect all forms in all languages into one big GADT (Expr). Then
-- project out subsets of those forms into new languages (L1, L2, etc)
-- by indexing the type constructors in Expr with constraints listing
-- which languages that constructor is live in.

-- Type family that returns a constructor. Tells you if a LangProj
-- is in a list of LangProjs. 
type family IsIn (l :: LangProj) (ls :: [LangProj]) :: Constraint where
    IsIn l (l ': ls) = ()
    IsIn l (z ': ls) = IsIn l ls

-- Languages in our toy compiler: L1, L2, and L3
data LangProj = L1 | L2 | L3

type Var = String

-------------------------------------------------------------------------
-- The language
-------------------------------------------------------------------------

-- We want to remove Let after L1 and Dub after L2.
data Expr l a where
    Lit :: (IsIn l '[L1, L2, L3]) => a        -> Expr l a
    Let :: (IsIn l '[L1])         => Expr l a -> Var      -> Expr l a -> Expr l a
    Lam :: (IsIn l '[L1, L2, L3]) => Var      -> Expr l a -> Expr l a
    App :: (IsIn l '[L1, L2, L3]) => Expr l a -> Expr l a -> Expr l a
    Add :: (IsIn l '[L1, L2, L3]) => Expr l a -> Expr l a -> Expr l a
    Dub :: (IsIn l '[L1, L2])     => Expr l a -> Expr l a
    Ref :: (IsIn l '[L1, L2, L3]) => Var      -> Expr l a


-------------------------------------------------------------------------
-- The passes
-------------------------------------------------------------------------

-- Rewrite let into left-left-lambda
desugarLet :: Expr L1 a -> Expr L2 a
desugarLet (Let e v b) = App (Lam v (desugarLet b)) (desugarLet e)
desugarLet (Lit i)     = Lit i
desugarLet (Lam v b)   = Lam v (desugarLet b)
desugarLet (App a b)   = App (desugarLet a) (desugarLet b)
desugarLet (Add a b)   = Add (desugarLet a) (desugarLet b)
desugarLet (Dub a)     = Dub (desugarLet a)
desugarLet (Ref v)     = Ref v

-- Rewrite dub (double) into add
-- Notice how we don't get a warning for not matching on let!
desugarDub :: Expr L2 a -> Expr L3 a
desugarDub (Lit i)     = Lit i
desugarDub (Lam v b)   = Lam v (desugarDub b)
desugarDub (App a b)   = App (desugarDub a) (desugarDub b)
desugarDub (Add a b)   = Add (desugarDub a) (desugarDub b)
desugarDub (Dub a)     = let a' = desugarDub a in Add a' a'
desugarDub (Ref v)     = Ref v

-------------------------------------------------------------------------
-- Tests and boilerplate
-------------------------------------------------------------------------

testExpr1 :: Expr L1 Int
testExpr1 = (Let (Lit 1) "a" (Dub (Ref "a")))

testExpr2 :: Expr L2 Int
testExpr2 = (App (Lam "a" (Dub (Ref "a"))) (Lit 1))

testExpr3 :: Expr L3 Int
testExpr3 = (App (Lam "a" (Add (Ref "a") (Ref "a"))) (Lit 1))

testExpr2' :: Expr L2 Int
testExpr2' = desugarLet testExpr1

testExpr3' :: Expr L3 Int
testExpr3' = desugarDub testExpr2'

instance Show a => Show (Expr l a) where
    show (Lit i) = "(Lit " ++ (show i) ++ ")"
    show (Let e v b) = "(Let " ++ (show e) ++ " " ++ (show v) ++ " " ++ (show b) ++ ")"
    show (Lam v b) = "(Lam " ++ (show v) ++ " " ++ (show b) ++ ")"
    show (App a b) = "(App " ++ (show a) ++ " " ++ (show b) ++ ")"
    show (Add a b) = "(Add " ++ (show a) ++ " " ++ (show b) ++ ")"
    show (Dub a) = "(Dub " ++ (show a) ++ ")"
    show (Ref v) = "(Ref " ++ (show v) ++ ")"
