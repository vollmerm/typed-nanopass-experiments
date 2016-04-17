{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE DataKinds       #-}

module Language.Nanopass where

import Data.Constraint

type family IsIn (l :: LangProj) (ls :: [LangProj]) :: Constraint where
    IsIn l (l ': ls) = ()
    IsIn l (z ': ls) = IsIn l ls
    
data LangProj = L1 | L2 | L3

type Var = String

data Expr l where
    Lit :: (IsIn l '[L1])         => Int    -> Expr l
    Let :: (IsIn l '[L1, L2, L3]) => Expr l -> Var    -> Expr l -> Expr l
    Lam :: (IsIn l '[L1, L2, L3]) => Var    -> Expr l -> Expr l
    Add :: (IsIn l '[L1, L2, L3]) => Expr l -> Expr l -> Expr l
    Dub :: (IsIn l '[L1, L2])     => Expr l -> Expr l
    Ref :: (IsIn l '[L1, L2, L3]) => Var    -> Expr l

testExpr1 :: Expr L1
testExpr1 = (Let (Lit 1) "a" (Add (Lit 2) (Ref "a")))
