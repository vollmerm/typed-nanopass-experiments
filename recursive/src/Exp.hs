{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Exp where

import Variants
import Variants.Case

import Control.Arrow
import Control.Monad
import Type.Class.Higher
import Type.Family.Constraint
import Type.Family.List
import Data.Type.Index
import Data.Type.Product
import Data.Function (fix)
import Data.Map (Map)
import qualified Data.Map as Map

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

{-
pattern Dub' :: (a ~ Int) => (DubF ∈ fs) => Rec fs Int -> Rec fs a
pattern Dub' a <- (prjRec -> Just (DUB a))
  where
  Dub' a = injRec $ DUB a

pattern Add' :: (a ~ Int) => (NumF ∈ fs) => Rec fs Int -> Rec fs Int -> Rec fs a
pattern Add' x y <- (prjRec -> Just (ADD x y))
  where
  Add' x y = injRec $ ADD x y

pattern Int' :: (a ~ Int) => (NumF ∈ fs) => Int -> Rec fs a
pattern Int' i <- (prjRec -> Just (INT i))
  where
  Int' i = injRec $ INT i

pattern IsZero' :: (a ~ Bool) => (NumF ∈ fs) => Rec fs Int -> Rec fs a
pattern IsZero' x <- (prjRec -> Just (ISZERO x))
  where
  IsZero' x = injRec $ ISZERO x

pattern If' :: () => (IfF ∈ fs) => Rec fs Bool -> Rec fs a -> Rec fs a -> Rec fs a
pattern If' t c a <- (prjRec -> Just (IF t c a))
  where
  If' t c a = injRec $ IF t c a

pattern Lam' :: (a ~ (b -> c)) => (LamF ∈ fs) => (Rec fs b -> Rec fs c) -> Rec fs a
pattern Lam' f <- (prjRec -> Just (LAM f))
  where
  Lam' f = injRec $ LAM f

pattern App' :: () => (LamF ∈ fs) => Rec fs (a -> b) -> Rec fs a -> Rec fs b
pattern App' x y <- (prjRec -> Just (APP x y))
  where
  App' x y = injRec $ APP x y

pattern Let' :: () => (LetF ∈ fs) => Rec fs a -> (Rec fs a -> Rec fs b) -> Rec fs b
pattern Let' a f <- (prjRec -> Just (LET a f))
  where
  Let' a f = injRec $ LET a f
-}

pattern Dub :: (a ~ Int) => (DubF ∈ fs) => r Int -> Variants fs r a
pattern Dub a <- (prj -> Just (DUB a))
  where
  Dub a = inj $ DUB a

pattern Add :: (a ~ Int) => (NumF ∈ fs) => r Int -> r Int -> Variants fs r a
pattern Add x y <- (prj -> Just (ADD x y))
  where
  Add x y = inj $ ADD x y

pattern Int :: (a ~ Int) => (NumF ∈ fs) => Int -> Variants fs r a
pattern Int i <- (prj -> Just (INT i))
  where
  Int i = inj $ INT i

pattern IsZero :: (a ~ Bool) => (NumF ∈ fs) => r Int -> Variants fs r a
pattern IsZero x <- (prj -> Just (ISZERO x))
  where
  IsZero x = inj $ ISZERO x

pattern If :: () => (IfF ∈ fs) => r Bool -> r a -> r a -> Variants fs r a
pattern If t c a <- (prj -> Just (IF t c a))
  where
  If t c a = inj $ IF t c a

{-
pattern Lam :: (a ~ (b -> c)) => (LamF ∈ fs) => (r b -> r c) -> Variants fs r a
pattern Lam f <- (prj -> Just (LAM f))
  where
  Lam f = inj $ LAM f

pattern App :: () => (LamF ∈ fs) => r (a -> b) -> r a -> Variants fs r b
pattern App x y <- (prj -> Just (APP x y))
  where
  App x y = inj $ APP x y

pattern Let :: () => (LetF ∈ fs) => r a -> (r a -> r b) -> Variants fs r b
pattern Let a f <- (prj -> Just (LET a f))
  where
  Let a f = inj $ LET a f
-}

-- desugarDub :: Exp1 a -> Exp2 a
desugarDub :: forall (fs :: [(* -> *) -> * -> *]) gs a.
  ( Handle DubF fs gs
  , NumF ∈ gs
  ) => Rec fs a -> Rec gs a
desugarDub = fix1 $ \rec ->
  cases
      $ ( \(DUB x) -> injRec $ ADD (rec x) (rec x)
        )
    -:: recursively rec

  -- cases
  --   $ ( \(DUB x) -> injRec $ ADD (desugarDub x) (desugarDub x)
  --     )
  -- -:: recursively desugarDub

{-
e1 :: (LamF ∈ fs) => Rec fs (a -> a)
e1 = Lam' $ \x -> x

e2 :: (LamF ∈ fs) => Rec fs ((a -> b) -> a -> b)
e2 = Lam' $ \f -> Lam' $ \x -> App' f x

e3 :: ('[IfF,NumF] ⊆ fs) => Rec fs Int
e3 = If' (IsZero' (Int' 3))
  (Add' (Int' 2) (Add' (Int' 1) (Int' 5)))
  (Add' (Int' 4) (Int' 1))
-}

{-
cases :: ((Rec fs a -> b) -> Variants fs (Rec fs) a -> b) -> Rec fs a -> b
cases f = fix $ \rec (Roll t) -> f rec t

everywhere :: HFunctors fs => Variants fs r a -> (r a -> Rec fs b) -> Rec fs b
everywhere e f = Roll $ hmap f e

recursive :: (HFoldables fs, f ∈ fs) => (f (Rec fs) a -> b) -> Rec fs a -> b
recursive f t = case prjRec t of
  Just u -> f u
  _      -> hfoldMap (recursive f) $ unroll t
-}

{-
desugarDub :: Exp1 a -> Exp2 a
desugarDub = \case
  Dub' x   -> Add' (desugarDub x) (desugarDub x)
  Add' x y -> Add' (desugarDub x) (desugarDub x)
  If' t c a -> If' (desugarDub t) (desugarDub c) (desugarDub a)
-}

{-
desugarDub :: Exp1 a -> Exp2 a
desugarDub = \case
  DUB x -> desugarDub x :+: desugarDub x
  -- fails to check, like it should.
  -- DUB (ISZERO x) -> desugarDub x :+: desugarDub x
  e     -> undefined
-}

