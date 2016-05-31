{-# LANGUAGE FunctionalDependencies #-}
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

module Variants.Case where

import Variants
import Type.Class.Known
import Type.Class.Higher
import Type.Family.List
import Data.Type.Index
import Data.Type.Length
import Data.Void
import Data.Profunctor
import Data.Profunctor.Sieve
import Control.Arrow

class (f ∈ fs) => Handle (f :: (k -> *) -> k -> *) (fs :: [(k -> *) -> k -> *]) (gs :: [(k -> *) -> k -> *]) | f fs -> gs where
  (-::) :: (f r a -> b) -> Cases gs r a b -> Cases fs r a b
infixr 0 -::

instance {-# OVERLAPPING #-} (gs ~ fs) => Handle f (f :< fs) gs where
  (-::) = (:::)

instance {-# OVERLAPPABLE #-} (Handle f fs gs, hs ~ (g :< gs)) => Handle f (g :< fs) hs where
  (-::) f = \case
    g ::: fs -> g ::: f -:: fs

(=::) :: forall f fs r a b. (f ∈ fs) => (f r a -> b) -> Cases fs r a b -> Cases fs r a b
(=::) f = go (elemIndex :: Index fs f)
  where
  go :: Index gs f -> Cases gs r a b -> Cases gs r a b
  go = \case
    IZ   -> \case
      _ ::: fs -> f ::: fs
    IS x -> \case
      g ::: fs -> g ::: go x fs
  {-# INLINE go #-}
{-# INLINE (=::) #-}
infixr 0 =::

data Cases (fs :: [(k -> *) -> k -> *]) :: (k -> *) -> k -> * -> * where
  Void  :: Cases Ø r a b
  (:::) :: (f r a -> b)
        -> Cases fs r a b
        -> Cases (f :< fs) r a b
infixr 0 :::

extractAt :: Index fs f -> Cases fs r a b -> f r a -> b
extractAt = \case
  IZ -> \case
    f ::: _ -> f
  IS x -> \case
    _ ::: fs -> extractAt x fs

{-
type CasesRec fs gs a b = Cases fs (Rec gs) a (Rec gs b)
-}

{-
recursivelyWith :: forall fs gs a. ListC (Functor1 <$> fs) => (forall x. Rec gs x -> Rec fs x) -> Length fs -> Cases fs (Rec gs) a (Rec fs a)
recursivelyWith f = \case
  LZ                   -> Void
  LS (l :: Length fs') -> _
    where
    r :: Cases fs' (Rec gs) a (Rec fs' a)
    r = recursivelyWith (_ . f) l
-}

recursivelyWith :: ListC (Functor1 <$> fs) => (forall x. Rec gs x -> Rec hs x) -> Subset fs hs -> Cases fs (Rec gs) a (Rec hs a)
recursivelyWith f = \case
  ØS      -> Void
  x :+ xs -> Roll . injWith x . map1 f ::: recursivelyWith f xs

recursively :: (ListC (Functor1 <$> fs), fs ⊆ hs) => (forall x. Rec gs x -> Rec hs x) -> Cases fs (Rec gs) a (Rec hs a)
recursively f = recursivelyWith f subset

{-
recursively :: ( => Cases
recursively = recursivelyWith subset
-}

variants :: Cases fs r a b -> Variants fs r a -> b
variants = \case
  Void -> noVariants
  f ::: fs -> \case
    L a -> f a
    R b -> variants fs b

cases :: Cases fs (Rec fs) a b -> Rec fs a -> b
cases fs = variants fs . unroll

fix1 :: forall f g a. (forall x. (forall y. f y -> g y) -> f x -> g x) -> f a -> g a
fix1 k = f
  where
  f :: forall x. f x -> g x
  f = k f

