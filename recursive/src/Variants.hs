{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
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

module Variants where

import Control.Arrow ((>>>))
import Control.Monad (MonadPlus(..))
import Type.Class.Higher
import Type.Family.List (type ListC , type Ø , type (:<) , type (<$>) , type (<&>))
import Data.Type.Index (Index(..), type (∈), Elem(..))

type Functors1 fs = ListC (Functor1 <$> fs)

data Cases (fs :: [(* -> *) -> * -> *]) (gs :: [(* -> *) -> * -> *]) :: * where
  Pass  :: Cases fs fs
  Match :: Remove f fs gs
        => (forall x. f (Rec hs) x -> Rec hs x)
        -> Cases gs hs
        -> Cases fs hs

class (f ∈ fs) => Remove (f :: (* -> *) -> * -> *) (fs :: [(* -> *) -> * -> *]) (gs :: [(* -> *) -> * -> *]) | fs f -> gs where
  without :: (f r a -> r b)
          -> (Variants gs r a -> r b)
          -> Variants fs r a -> r b
  without1 :: (forall x. f r x -> r x)
           -> (forall x. Variants gs r x -> r x)
           -> Variants fs r a -> r a

instance {-# OVERLAPPING #-} (gs ~ fs) => Remove f (f :< fs) gs where
  without f g = \case
    L a -> f a
    R b -> g b
  without1 f g = \case
    L a -> f a
    R b -> g b

instance {-# OVERLAPPABLE #-} (hs ~ (g :< gs), Remove f fs gs) => Remove f (g :< fs) hs where
  without f g = \case
    L a -> g $ L a
    R b -> without f (g . R) b
  without1 f g = \case
    L a -> g $ L a
    R b -> without f (g . R) b

everywhere :: ListC (Functor1 <$> fs) => Cases fs gs -> Rec fs a -> Rec gs a
everywhere c = unroll >>> map1 (everywhere c) >>> everywhere' c

everywhere' :: Cases fs gs -> Variants fs (Rec gs) a -> Rec gs a
everywhere' = \case
  Pass       -> Roll
  Match f fs -> without f $ everywhere' fs


type as ⊆ bs = ListC (Elem bs <$> as)
infix 4 ⊆

variant :: (Functor1 f, f ∈ fs) => (forall x. r x -> s x) -> f r a -> Variants fs s a
variant f = inj . map1 f

variants :: (ListC (Functor1 <$> fs), fs ⊆ gs) => (forall x. r x -> s x) -> Variants fs r a -> Variants gs s a
variants f = \case
  L a -> variant  f a
  R b -> variants f b

boilerplate :: (ListC (Functor1 <$> fs), fs ⊆ gs) => (forall x. Rec fs x -> Rec gs x) -> Rec fs a -> Rec gs a
boilerplate f = Roll . variants f . unroll

-- Variants {{{

type FunctorsOn r fs = ListC (Functor <$> fs <&> r)

data Variants :: [(* -> *) -> * -> *] -> (* -> *) -> * -> * where
  L :: !(f r a)
    -> Variants (f :< fs) r a
  R :: !(Variants fs r a)
    -> Variants (f :< fs) r a

deriving instance ListC (Eq <$> fs <&> r <&> a)
  => Eq (Variants fs r a)
deriving instance
  ( ListC (Eq  <$> fs <&> r <&> a)
  , ListC (Ord <$> fs <&> r <&> a)
  ) => Ord (Variants fs r a)
deriving instance ListC (Show <$> fs <&> r <&> a)
  => Show (Variants fs r a)

instance FunctorsOn r fs => Functor (Variants fs r) where
  fmap f = \case
    L a -> L $ f <$> a
    R b -> R $ f <$> b

instance ListC (Functor1 <$> fs) => Functor1 (Variants fs) where
  map1 f = \case
    L a -> L (map1 f a)
    R b -> R (map1 f b)

emptyVariants :: Variants Ø r a -> b
emptyVariants _ = error "impossible: Variants Ø"

data El (gs :: [k -> l -> *]) :: k -> l -> * where
  El :: !(Index gs f)
     -> !(f r a)
     -> El gs r a

imapVariants :: (forall f. Index fs f -> f r a -> El gs s b)
             -> Variants fs r a -> Variants gs s b
imapVariants f = \case
  L a -> case f IZ a of
    El y b -> injWith y b
  R b -> imapVariants (f . IS) b

ifoldVariants :: (forall f. Index fs f -> f r a -> m)
                 -> Variants fs r a -> m
ifoldVariants f = \case
  L a -> f IZ a
  R b -> ifoldVariants (f . IS) b

itraverseVariants :: Functor g => (forall f. Index fs f -> f r a -> g (El gs s b))
                  -> Variants fs r a -> g (Variants gs s b)
itraverseVariants f = \case
  L a ->
    ( \case
      El y b -> injWith y b
    ) <$> f IZ a
  R b -> itraverseVariants (f . IS) b

inj :: (f ∈ fs) => f r a -> Variants fs r a
inj = injWith elemIndex

prj :: (f ∈ fs, MonadPlus m) => Variants fs r a -> m (f r a)
prj = prjWith elemIndex

injWith :: Index fs f -> f r a -> Variants fs r a
injWith = \case
  IZ   -> L
  IS x -> R . injWith x

prjWith :: MonadPlus m => Index fs f -> Variants fs r a -> m (f r a)
prjWith = \case
  IZ   -> \case
    L a -> return a
    _   -> mzero
  IS x -> \case
    R a -> prjWith x a
    _   -> mzero

injSubWith :: (forall f. Index fs f -> Index gs f) -> Variants fs r a -> Variants gs r a
injSubWith f = \case
  L a -> injWith (f IZ) a
  R b -> injSubWith (f . IS) b

prjSubWith :: MonadPlus m => (forall f. Index gs f -> m (Index fs f)) -> Variants gs r a -> m (Variants fs r a)
prjSubWith f = \case
  L a -> do
    x <- f IZ
    return $ injWith x a
  R b -> prjSubWith (f . IS) b

-- }}}

-- Rec {{{

data Rec :: [(* -> *) -> * -> *] -> * -> * where
  Roll :: { unroll :: Variants fs (Rec fs) a
          } -> Rec fs a

emptyRec :: Rec Ø a -> b
emptyRec = emptyVariants . unroll

imapRec :: (forall f. Index fs f -> f (Rec fs) a -> El gs (Rec gs) b)
        -> Rec fs a -> Rec gs b
imapRec f = Roll . imapVariants f . unroll

ifoldRec :: (forall f. Index fs f -> f (Rec fs) a -> m)
         -> Rec fs a -> m
ifoldRec f = ifoldVariants f . unroll

itraverseRec :: Functor g => (forall f. Index fs f -> f (Rec fs) a -> g (El gs (Rec gs) b))
             -> Rec fs a -> g (Rec gs b)
itraverseRec f = fmap Roll . itraverseVariants f . unroll

injRec :: (f ∈ fs) => f (Rec fs) a -> Rec fs a
injRec = Roll . inj

prjRec :: (MonadPlus m, f ∈ fs) => Rec fs a -> m (f (Rec fs) a)
prjRec = prj . unroll

-- }}}

fix1 :: forall f g a. (forall x. (forall y. f y -> g y) -> f x -> g x) -> f a -> g a
fix1 k = f
  where
  f :: forall x. f x -> g x
  f = k f

