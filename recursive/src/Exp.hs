{-# LANGUAGE ConstraintKinds #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
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

import Control.Monad.Fix
import Type.Class.Higher (Functor1(..))
import Data.Type.Index (type (∈),Index(..))
import Data.Functor.Constant
import Data.Function (fix)
import Data.Typeable
import Data.Maybe (fromJust)

desugarDub ::
  ( Functors1 l_1
  , Remove DubF l_1 l_2
  , NumF ∈ l_2
  ) => Rec l_1 a -> Rec l_2 a
desugarDub = everywhere
  $ Elim ? \case
    DUB x -> Add x x
  $ Pass

desugarLet ::
  ( Functors1 l_1
  , Remove LetF l_1 l_2
  , LamF ∈ l_2
  ) => Rec l_1 a -> Rec l_2 a
desugarLet = everywhere
  $ Elim ? \case
    LET x a b -> App (Lam x b) a
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
  $ Elim ? \case
    DUB x -> Add x x
  $ Elim ? \case
    LET x a b -> App (Lam x b) a
  $ Pass

swapAdd ::
  ( All Functor1 l
  , NumF ∈ l
  ) => Rec l a -> Rec l a
swapAdd = everywhere
  $ Match ? \case
    ADD x y -> Add y x
  $ Pass

class Render (f :: (* -> *) -> * -> *) where
  render :: f (Constant ShowS) a -> Constant ShowS a

renderAll :: (All Render fs, All Functor1 fs) => Rec fs a -> String
renderAll = ($ "") . getConstant . byClass (undefined :: prx Render) render

byClass :: forall prx c fs r a. (All c fs, All Functor1 fs) => prx c -> (forall f x. c f => f r x -> r x) -> Rec fs a -> r a
byClass p f = go . map1 (byClass p f) . unroll
  where
  go :: forall gs x. All c gs => Variants gs r x -> r x
  go = \case
    L a -> f a
    R b -> go b

data Val :: * where
  Val :: Typeable a => a -> Val

data Eval :: (* -> *) -> * -> * where
  EV :: ((forall x. Typeable x => String -> Maybe x) -> a) -> Eval r a

pattern Ev f <- (prjRec -> Just (EV f))
  where
  Ev f = injRec $ EV f

eval :: Exp1 a -> a
eval e = case eval' e of
  Ev a -> a $ const Nothing

eval' :: Exp1 a -> Rec '[Eval] a
eval' = everywhere
  $ Elim ? \case
    LAM x (Ev b)      -> Ev $ \k a -> b $ \y -> if x == y then cast a else k y
    APP (Ev a) (Ev b) -> Ev $ \k -> a k (b k)
    VAR x             -> Ev $ \k -> case k x of
      Just v -> v
      _      -> error $ "unbound variable: " ++ x
  $ Elim ? \case
    DUB (Ev x)        -> Ev $ \k -> x k + x k
  $ Elim ? \case
    IF (Ev t) (Ev c) (Ev a) -> Ev $ \k -> if t k then c k else a k
  $ Elim ? \case
    LET x (Ev a) (Ev b) -> Ev $ \k -> b $ \y -> if x == y then cast (a k) else k y
  $ Elim ? \case
    INT i             -> Ev $ \_ -> i
    ADD (Ev x) (Ev y) -> Ev $ \k -> x k + y k
    ISZERO (Ev x)     -> Ev $ \k -> x k == 0
  $ Total

-- type is inferred with NoMonomorphismRestriction
-- e1 :: ('[LamF,DubF] ⊆ l_1) => Rec l_1 (a -> Int)
e1 :: Exp1 (Int -> Int)
e1 = Lam "x" (Dub (Var "x"))

e1' :: Exp2 (Int -> Int)
e1' = desugarDub e1

e2 :: Exp1 Int
e2 = Let "x" (Int 3) (Dub (Var "x"))

data ShowF :: (* -> *) -> * -> * where
  SHOW :: String -> ShowF r a

pattern Sh x <- (prjRec -> Just (SHOW x))
  where
  Sh x = injRec $ SHOW x

getShow :: Rec '[ShowF] a -> String
getShow (Sh s) = s

data LamF r a where
  VAR :: Typeable a
      => String -> LamF r a
  LAM :: Typeable a
      => String -> r b -> LamF r (a -> b)
  APP :: r (a -> b) -> r a -> LamF r b

instance Render LamF where
  render = \case
    VAR x    -> Constant $ showString x
    LAM x b -> Constant $ showParen True
      $ showChar '\\'
      . showString x
      . showString " -> "
      . getConstant b
    APP a b -> Constant $ showParen True
      $ getConstant a
      . showChar ' '
      . getConstant b

instance Functor1 LamF where
  map1 f = \case
    VAR x   -> VAR x
    LAM x b -> LAM x (f b)
    APP a b -> APP (f a) (f b)

data LetF r a where
  LET :: Typeable a => String -> r a -> r b -> LetF r b

instance Render LetF where
  render (LET x a b) = Constant $ showParen True
    $ showString "let "
    . showString x
    . showString " = "
    . getConstant a
    . showString " in "
    . getConstant b

instance Functor1 LetF where
  map1 f (LET x a b) = LET x (f a) (f b)

data IfF r a where
  IF :: r Bool -> r a -> r a -> IfF r a

instance Render IfF where
  render (IF t c a) = Constant $ showParen True
    $ showString "if "
    . getConstant t
    . showString " then "
    . getConstant c
    . showString " else "
    . getConstant a

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

instance Render NumF where
  render = \case
    INT i    -> Constant $ shows i
    ADD x y  -> Constant $ showParen True
      $ getConstant x
      . showString " + "
      . getConstant y
    ISZERO x -> Constant $ showParen True
      $ showString "isZero "
      . getConstant x

data DubF r a where
  DUB :: r Int -> DubF r Int

instance Functor1 DubF where
  map1 f (DUB x) = DUB (f x)

instance Render DubF where
  render (DUB x) = Constant $ showParen True
    $ showString "dub "
    . getConstant x

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

(?) :: ((forall x. f x -> g x) -> b) -> (forall x. f x -> g x) -> b
f ? g = f g
infixr 1 ?

(??) :: (a -> b) -> a -> b
(??) = ($)
infixr 1 ??

