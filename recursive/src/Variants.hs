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
import Type.Family.Constraint (type Constraint, ØC)
import Type.Family.List (type ListC , type Ø , type (:<) , type (<$>) , type (<&>))
import Data.Type.Index (Index(..), type (∈), Elem(..))

type All    c as     = ListC (c <$> as)
type AllOp  c as x   = ListC (c <$> as <&> x)
type AllOp2 c as x y = ListC (c <$> as <&> x <&> y)

type Functors1 fs = All Functor1 fs

data Match (fs :: [(* -> *) -> * -> *]) (r :: * -> *) :: * -> * -> * where
  Total :: Match Ø r a b
  Elim  :: Remove f fs gs
        => (f r a -> b)
        -> Match gs r a b
        -> Match fs r a b
  Match :: (f ∈ fs)
        => (f r a -> b)
        -> Match fs r a b
        -> Match fs r a b
  Pass :: Match fs (Rec fs) a (Rec fs a)
  Else :: (Variants fs r a -> b)
       -> Match fs r a b

data Recursive (fs :: [(* -> *) -> * -> *]) (gs :: [(* -> *) -> * -> *]) :: * where
  PassRec  :: Recursive fs fs
  TotalRec :: Recursive Ø gs
  ElimRec  :: Remove f fs gs
           => (forall x. f (Rec hs) x -> Rec hs x)
           -> Recursive gs hs
           -> Recursive fs hs
  MatchRec :: (f ∈ fs)
           => (forall x. f (Rec gs) x -> Rec gs x)
           -> Recursive fs gs
           -> Recursive fs gs
  ElseRec  :: (forall x. Variants fs (Rec gs) x -> Rec gs x)
           -> Recursive fs gs

class (f ∈ fs) => Remove (f :: (* -> *) -> * -> *) (fs :: [(* -> *) -> * -> *]) (gs :: [(* -> *) -> * -> *]) | fs f -> gs where
  without :: (f r a -> b)
          -> (Variants gs r a -> b)
          -> Variants fs r a -> b
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

match :: Match fs (Rec fs) a b -> Rec fs a -> b
match c = match' c . unroll

match' :: Match fs r a b -> Variants fs r a -> b
match' = \case
  Total      -> emptyVariants
  Elim  f fs -> without f $ match' fs
  Match f fs -> replaceAt f (match' fs) elemIndex
  Pass       -> Roll
  Else f     -> f

everywhere :: All Functor1 fs => Recursive fs gs -> Rec fs a -> Rec gs a
everywhere c = unroll >>> map1 (everywhere c) >>> everywhere' c

everywhere' :: Recursive fs gs -> Variants fs (Rec gs) a -> Rec gs a
everywhere' = \case
  PassRec       -> Roll
  TotalRec      -> emptyVariants
  ElimRec  f fs -> without f $ everywhere' fs
  MatchRec f fs -> replaceAt1 f (everywhere' fs) elemIndex
  ElseRec  f    -> f

foldRec1 :: All Functor1 fs => (forall f x. Index fs f -> f r x -> r x) -> Rec fs a -> r a
foldRec1 f = foldVariants1 f . map1 (foldRec1 f) . unroll

foldVariants1 :: (forall f x. Index fs f -> f r x -> s x) -> Variants fs r a -> s a
foldVariants1 f = \case
  L a -> f IZ a
  R b -> foldVariants1 (f . IS) b

replaceAt :: (f r a -> b) -> (Variants fs r a -> b) -> Index fs f -> Variants fs r a -> b
replaceAt f k = \case
  IZ   -> \case
    L a -> f a
    R b -> k $ R b
  IS x -> \case
    L a -> k $ L a
    R b -> replaceAt f (k . R) x b

replaceAt1 :: (forall x. f r x -> s x) -> (forall x. Variants fs r x -> s x) -> Index fs f -> Variants fs r a -> s a
replaceAt1 f k = \case
  IZ   -> \case
    L a -> f a
    R b -> k $ R b
  IS x -> \case
    L a -> k $ L a
    R b -> replaceAt1 f (k . R) x b

type as ⊆ bs = All (Elem bs) as
infix 4 ⊆

variant :: (Functor1 f, f ∈ fs) => (forall x. r x -> s x) -> f r a -> Variants fs s a
variant f = inj . map1 f

variants :: (All Functor1 fs, fs ⊆ gs) => (forall x. r x -> s x) -> Variants fs r a -> Variants gs s a
variants f = \case
  L a -> variant  f a
  R b -> variants f b

boilerplate :: (All Functor1 fs, fs ⊆ gs) => (forall x. Rec fs x -> Rec gs x) -> Rec fs a -> Rec gs a
boilerplate f = Roll . variants f . unroll

-- Variants {{{

data Variants :: [(* -> *) -> * -> *] -> (* -> *) -> * -> * where
  L :: !(f r a)
    -> Variants (f :< fs) r a
  R :: !(Variants fs r a)
    -> Variants (f :< fs) r a

deriving instance AllOp2 Eq fs r a -- ListC (Eq <$> fs <&> r <&> a)
  => Eq (Variants fs r a)
deriving instance
  ( ListC (Eq  <$> fs <&> r <&> a)
  , ListC (Ord <$> fs <&> r <&> a)
  ) => Ord (Variants fs r a)
deriving instance ListC (Show <$> fs <&> r <&> a)
  => Show (Variants fs r a)

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

foldVariants :: (forall f. Index fs f -> f r a -> m)
                 -> Variants fs r a -> m
foldVariants f = \case
  L a -> f IZ a
  R b -> foldVariants (f . IS) b

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

foldRec :: (forall f. Index fs f -> f (Rec fs) a -> m)
         -> Rec fs a -> m
foldRec f = foldVariants f . unroll

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

class HFunctor (f :: (k -> *) -> k -> *) where
  hmap :: (r a -> s b) -> f r a -> f s b

instance All HFunctor fs => HFunctor (Variants fs) where
  hmap f = \case
    L a -> L $ hmap f a
    R b -> R $ hmap f b

class HFoldable (f :: (k -> *) -> k -> *) where
  hfoldMap :: Monoid m => (r a -> m) -> f r a -> m

instance All HFoldable fs => HFoldable (Variants fs) where
  hfoldMap f = \case
    L a -> hfoldMap f a
    R b -> hfoldMap f b

