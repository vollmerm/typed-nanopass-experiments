{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Lang where

import           Prelude        hiding (length, map, max, min, not, sum, zip,
                                 zipWith, (==))
import qualified Prelude

import           Data.Tree
import           Data.Typeable

import           Data.Syntactic hiding (drawAST, fold, printExpr, showAST,
                                 writeHtmlAST)
import qualified Data.Syntactic as Syntactic
-- import           Data.Syntactic.Functional
-- import           Data.Syntactic.Sugar.BindingT ()

class    (Typeable a, Show a, Eq a, Ord a) => Type a
instance (Typeable a, Show a, Eq a, Ord a) => Type a

data Arithmetic sig
  where
    Plus  :: (Type a, Num a) => Arithmetic (a :-> a :-> Full a)
    Times :: (Type a, Num a) => Arithmetic (a :-> a :-> Full a)

data Arithmetic' sig
  where
    Dub :: (Type a, Num a) => Arithmetic' (a :-> Full a)

data Let sig
  where
    Let :: Let (a :-> a :-> Full a)

data Bind sig
  where
    Lamb :: Bind (a :-> Full a)
    Var  :: Bind (Int :-> Full a)

type L1 = Arithmetic :+: Arithmetic' :+: Let :+: Bind
type L2 = Arithmetic :+: Let :+: Bind
type L3 = Arithmetic :+: Bind

instance Symbol Arithmetic
  where
    symSig Plus  = signature
    symSig Times = signature

instance Symbol Arithmetic'
  where
    symSig Dub = signature

instance Render Arithmetic
  where
    renderSym Plus = "(+)"
    renderSym Times = "(*)"
    renderArgs = renderArgsSmart

instance Symbol Let
  where
    symSig Let = signature

instance Equality Let
  where
    equal = equalDefault
    hash  = hashDefault

instance Render Let
  where
    renderSym Let = "let"

instance Symbol Bind
  where
    symSig Lamb = signature
    symSig Var = signature

instance Render Bind
  where
    renderSym Lamb = "lamb"
    renderSym Var = "var"

