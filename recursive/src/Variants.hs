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

import Control.Arrow
import Control.Monad
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Data.Type.Index

-- Variants {{{

data Variants :: [(k -> *) -> k -> *] -> (k -> *) -> k -> * where
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

none :: Variants Ø r a -> b
none _ = error "impossible: Variants Ø"

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

injSub :: (fs ⊆ gs) => Variants fs r a -> Variants gs r a
injSub = injSubWith liftIndex

prjSub :: (MonadPlus m, fs ⊆ gs) => Variants gs r a -> m (Variants fs r a)
prjSub = prjSubWith lowerIndex

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

data Rec :: [(k -> *) -> k -> *] -> k -> * where
  Roll :: { unroll :: Variants fs (Rec fs) a
          } -> Rec fs a

foldRec :: (HFoldables fs, f ∈ fs)
        => (f (Rec fs) a -> b)
        -> Rec fs a -> b
foldRec f t = case prjRec t of
  Just u -> f u
  _      -> hfoldMap (foldRec f) $ unroll t

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

supRec :: (HFunctors gs, fs ⊆ gs) => Rec fs a -> Rec gs a
supRec = Roll . hmap supRec . injSub . unroll

subRec :: (HTraversables fs, MonadPlus m, fs ⊆ gs) => Rec gs a -> m (Rec fs a)
subRec = fmap Roll . (>>= htraverse subRec) . prjSub . unroll

-- }}}

-- Injection/Projection {{{

liftIndex :: (fs ⊆ gs) => Index fs f -> Index gs f
liftIndex = \case
  IZ   -> elemIndex
  IS x -> liftIndex x

class SubsetC fs gs => (fs :: [k]) ⊆ (gs :: [k]) where
  type SubsetC fs gs :: Constraint
  lowerIndex :: MonadPlus m => Index gs f -> m (Index fs f)
infix 4 ⊆

instance Ø ⊆ gs where
  type SubsetC Ø gs = ØC
  lowerIndex _ = mzero

instance (f ∈ gs, fs ⊆ gs) => (f :< fs) ⊆ gs where
  type SubsetC (f :< fs) gs = (f ∈ gs, fs ⊆ gs)
  lowerIndex = go elemIndex
    where
    go :: MonadPlus m => Index hs f -> Index hs g -> m (Index (f :< fs) g)
    go = curry $ \case
      (IZ  ,IZ  ) -> return IZ
      (IZ  ,IS _) -> mzero
      (IS _,IZ  ) -> mzero
      (IS x,IS y) -> go x y

-- }}}

-- HFunctor {{{

class HFunctor (t :: (k -> *) -> k -> *) where
  hmap :: (f a -> g b) -> t f a -> t g b

class HFoldable (t :: (k -> *) -> k -> *) where
  hfoldMap :: (f a -> m) -> t f a -> m

class (HFunctor t, HFoldable t) => HTraversable (t :: (k -> *) -> k -> *) where
  htraverse :: Applicative h => (f a -> h (g b))
            -> t f a -> h (t g b)

type HFunctors fs = ListC (HFunctor <$> fs)
type HFoldables fs = ListC (HFoldable <$> fs)
type HTraversables fs = (HFunctors fs, HFoldables fs, ListC (HTraversable <$> fs))

instance HFunctors fs => HFunctor (Variants fs) where
  hmap f = \case
    L a -> L $ hmap f a
    R b -> R $ hmap f b

instance HFoldables fs => HFoldable (Variants fs) where
  hfoldMap f = \case
    L a -> hfoldMap f a
    R b -> hfoldMap f b

instance HTraversables fs => HTraversable (Variants fs) where
  htraverse f = \case
    L a -> L <$> htraverse f a
    R b -> R <$> htraverse f b

-- }}}

