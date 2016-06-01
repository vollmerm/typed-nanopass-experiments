{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Exp where

import Variants

import Type.Class.Higher (Functor1(..))
import Data.Type.Index (type (∈))

desugarDub ::
  ( Functors1 l_1
  , Remove DubF l_1 l_2
  , NumF ∈ l_2
  ) => Rec l_1 a -> Rec l_2 a
desugarDub = everywhere
  $ Match ( \(DUB x) -> Add x x )
  $ Pass

desugarLet ::
  ( Functors1 l_1
  , Remove LetF l_1 l_2
  , LamF ∈ l_2
  ) => Rec l_1 a -> Rec l_2 a
desugarLet = everywhere
  $ Match ( \(LET x a b) -> App (Lam x b) a )
  $ Pass

desugarDubLet ::
  ( Functors1 l_1
  , Remove DubF l_1 l_2
  , Remove LetF l_2 l_3
  , LamF ∈ l_3
  , NumF ∈ l_3
  ) => Rec l_1 a -> Rec l_3 a
-- desugarDubLet :: Exp1 a -> Exp3 a
desugarDubLet = everywhere
  $ Match ( \(DUB x) -> Add x x )
  $ Match ( \(LET x a b) -> App (Lam x b) a )
  $ Pass



data LamF r a where
  VAR :: String -> LamF r a
  LAM :: String -> r b -> LamF r (a -> b)
  APP :: r (a -> b) -> r a -> LamF r b

instance Functor1 LamF where
  map1 f = \case
    VAR x   -> VAR x
    LAM x b -> LAM x (f b)
    APP a b -> APP (f a) (f b)

data LetF r a where
  LET :: String -> r a -> r b -> LetF r b

instance Functor1 LetF where
  map1 f (LET x a b) = LET x (f a) (f b)

data IfF r a where
  IF :: r Bool -> r a -> r a -> IfF r a

instance Functor1 IfF where
  map1 f (IF t c a) = IF (f t) (f c) (f a)

data NumF r a where
  INT    :: Int -> NumF r Int
  ADD    :: r Int -> r Int -> NumF r Int
  ISZERO :: r Int -> NumF r Bool

instance Functor1 NumF where
  map1 f = \case
    INT i    -> INT i
    ADD x y  -> ADD (f x) (f y)
    ISZERO x -> ISZERO (f x)

data DubF r a where
  DUB :: r Int -> DubF r Int

instance Functor1 DubF where
  map1 f (DUB x) = DUB (f x)

type L1 = '[DubF,LamF,LetF,IfF,NumF]
type L2 = '[LamF,LetF,IfF,NumF]
type L3 = '[LamF,IfF,NumF]

type Exp1 = Rec L1
type Exp2 = Rec L2
type Exp3 = Rec L3

-- pattern Dub :: (a ~ Int) => (DubF ∈ fs) => Rec fs Int -> Rec fs a
pattern Dub a <- (prjRec -> Just (DUB a))
  where
  Dub a = injRec $ DUB a

-- pattern Add :: (a ~ Int) => (NumF ∈ fs) => Rec fs Int -> Rec fs Int -> Rec fs a
pattern Add x y <- (prjRec -> Just (ADD x y))
  where
  Add x y = injRec $ ADD x y

-- pattern Int :: (a ~ Int) => (NumF ∈ fs) => Int -> Rec fs a
pattern Int i <- (prjRec -> Just (INT i))
  where
  Int i = injRec $ INT i

-- pattern IsZero :: (a ~ Bool) => (NumF ∈ fs) => Rec fs Int -> Rec fs a
pattern IsZero x <- (prjRec -> Just (ISZERO x))
  where
  IsZero x = injRec $ ISZERO x

-- pattern If :: () => (IfF ∈ fs) => Rec fs Bool -> Rec fs a -> Rec fs a -> Rec fs a
pattern If t c a <- (prjRec -> Just (IF t c a))
  where
  If t c a = injRec $ IF t c a

pattern Lam x b <- (prjRec -> Just (LAM x b))
  where
  Lam x b = injRec $ LAM x b

pattern App a b <- (prjRec -> Just (APP a b))
  where
  App a b = injRec $ APP a b

pattern Var x <- (prjRec -> Just (VAR x))
  where
  Var x = injRec $ VAR x

pattern Let x a b <- (prjRec -> Just (LET x a b))
  where
  Let x a b = injRec $ LET x a b

