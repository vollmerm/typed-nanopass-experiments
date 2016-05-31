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

module Data.Fix where

import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Data.Type.Index
import Data.Type.Length

import Prelude hiding (id,(.))
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Profunctor
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Distributive

type Functors     fs = ListC (Functor     <$> fs)
type Applicatives fs = ListC (Applicative <$> fs)
type Foldables    fs = ListC (Foldable    <$> fs)
type Traversables fs = ListC (Traversable <$> fs)
type Comonads     fs = ListC (Comonad     <$> fs)

-- Fix {{{

data Fix (fs :: [* -> *]) :: * where
  Fix :: { unFix :: !(Sum fs (Fix fs)) }
      -> Fix fs

inject :: (Functor f, f ∈ fs) => f (Fix fs) -> Fix fs
inject = Fix . inj

subFix :: (fs ⊆ gs) => Fix fs -> Fix gs
subFix = Fix . subSum . fmap subFix . unFix

subFixOp :: (fs ⊆ gs) => (Fix gs -> a) -> Fix fs -> a
subFixOp f = f . subFix

fixHead :: Functor f => f (Fix (f :< fs)) -> Fix (f :< fs)
fixHead = Fix . inHead

fixTail :: Fix fs -> Fix (f :< fs)
fixTail = Fix . inTail . fmap fixTail . unFix

-- }}}

-- Sum {{{

data Sum (fs :: [* -> *]) :: * -> * where
  In :: Functor f
     => !(Index fs f)
     -> !(f a)
     -> Sum fs a

inj :: (Functor f, f ∈ fs) => f a -> Sum fs a
inj = In elemIndex

inHead :: Functor f => f a -> Sum (f :< fs) a
inHead = In IZ
{-# INLINE inHead #-}

inTail :: Sum fs a -> Sum (f :< fs) a
inTail (In x t) = In (IS x) t
{-# INLINE inTail #-}

subSum :: (fs ⊆ gs) => Sum fs a -> Sum gs a
subSum (In x t) = In (subIndex x) t

subSumOp :: (fs ⊆ gs) => (Sum gs a -> b) -> Sum fs a -> b
subSumOp f = f . subSum

instance Functor (Sum fs) where
  fmap f (In x t) = In x $ f <$> t

instance (Comonads fs, Known Length fs) => Category (Matches fs) where
  id = go (known :: Length fs)
    where
    go :: Comonads gs => Length gs -> Matches gs a a
    go = \case
      LZ   -> Void
      LS l -> extract ::: go l
    {-# INLINE go #-}
  {-# INLINE id #-}
  (.) = curry $ \case
    (Void,Void) -> Void
    (g ::: gs,f ::: fs) -> (g =<= f) ::: (gs . fs)
  {-# INLINE (.) #-}

instance Comonads fs => Comonad (Sum fs) where
  extract (In x t) = go x t
    where
    go :: Comonads gs => Index gs g -> g a -> a
    go = \case
      IZ   -> extract
      IS x -> go x
    {-# INLINE go #-}
  {-# INLINE extract #-}
  duplicate (In x t) = go x t
    where
    go :: Comonads gs => Index gs g -> g a -> Sum gs (Sum gs a)
    go = \case
      IZ   -> inHead . fmap inHead . duplicate
      IS x -> inTail . fmap inTail . go x
    {-# INLINE go #-}
  {-# INLINE duplicate #-}

-- }}}

-- Matches {{{

data Matches (fs :: [* -> *]) :: * -> * -> * where
  Void  :: Matches Ø a b
  (:::) :: Functor f
        => (f a -> b)
        -> Matches fs a b
        -> Matches (f :< fs) a b
infixr 0 :::

(>::) :: forall f fs a b. (f ∈ fs) => (f a -> b) -> Matches fs a b -> Matches fs a b
(>::) f = go (elemIndex :: Index fs f)
  where
  go :: Index gs f -> Matches gs a b -> Matches gs a b
  go = \case
    IZ   -> \case
      _ ::: fs -> f ::: fs
    IS x -> \case
      g ::: fs -> g ::: go x fs
  {-# INLINE go #-}
infixr 0 >::

(&:&) :: Matches fs a b -> Matches fs a c -> Matches fs a (b,c)
(&:&) = curry $ \case
  (Void,Void) -> Void
  (f ::: fs,g ::: gs) -> ((,) <$> f <*> g) ::: (fs &:& gs)
{-# INLINE (&:&) #-}
infixr 3 &:&

extractAt :: Index fs f -> Matches fs a b -> (f a -> b)
extractAt = \case
  IZ   -> \case
    f ::: _ -> f
  IS x -> \case
    _ ::: fs -> extractAt x fs
{-# INLINE extractAt #-}

-- }}}

-- Matches instances {{{

instance Functor (Matches fs a) where
  fmap = rmap

instance (Functors fs, Known Length fs) => Applicative (Matches fs a) where
  pure (b :: b) = go (known :: Length fs)
    where
    go :: Functors gs => Length gs -> Matches gs a b
    go = \case
      LZ   -> Void
      LS l -> const b ::: go l
    {-# INLINE go #-}
  {-# INLINE pure #-}
  (<*>) = curry $ \case
    (Void,Void) -> Void
    (f ::: fs, a ::: as) -> (f <*> a) ::: (fs <*> as)
  {-# INLINE (<*>) #-}

{-
instance (Functors fs, Known Length fs, a ~ Fix fs) => Monad (Matches fs a) where
  fs >>= k = case fs of
    Void      -> Void
    f ::: fs' -> _ ::: _
-}

instance (Functors fs, Known Length fs) => Distributive (Matches fs a) where
  distribute = go (known :: Length fs)
    where
    go :: (Functor f, Functors gs) => Length gs -> f (Matches gs a b) -> Matches gs a (f b)
    go = \case
      LZ   -> pure Void
      LS l -> (:::) <$> (\m a -> flip (extractAt IZ) a <$> m) <*> go l . fmap (\(_ ::: m) -> m)
    {-# INLINE go #-}
  {-# INLINE distribute #-}

instance Profunctor (Matches fs) where
  dimap l r = \case
    Void    -> Void
    f ::: fs -> asCostar (dimap l r) f ::: dimap l r fs
  {-# INLINE dimap #-}
  lmap l = \case
    Void    -> Void
    f ::: fs -> asCostar (lmap l) f ::: lmap l fs
  {-# INLINE lmap #-}
  rmap r = \case
    Void    -> Void
    f ::: fs -> asCostar (rmap r) f ::: rmap r fs
  {-# INLINE rmap #-}

instance Costrong (Matches fs) where
  unfirst = \case
    Void     -> Void
    f ::: fs -> asCostar unfirst f ::: unfirst fs
  {-# INLINE unfirst #-}

instance Closed (Matches fs) where
  closed = \case
    Void     -> Void
    f ::: fs -> asCostar closed f ::: closed fs
  {-# INLINE closed #-}

instance Cosieve (Matches fs) (Sum fs) where
  cosieve fs (In x t) = extractAt x fs t

instance (Functors fs, Known Length fs) => Corepresentable (Matches fs) where
  type Corep (Matches fs) = Sum fs
  cotabulate = go (known :: Length fs)
    where
    go :: Functors gs => Length gs -> (Sum gs a -> b) -> Matches gs a b
    go = \case
      LZ   -> \_ -> Void
      LS l -> \f -> f . inHead ::: go l (f . inTail)

instance Applicatives fs => Cochoice (Matches fs) where
  unleft = \case
    Void     -> Void
    f ::: fs -> asCostar unleft f ::: unleft fs
  {-# INLINE unleft #-}

instance Traversables fs => Choice (Matches fs) where
  left' = \case
    Void     -> Void
    f ::: fs -> asCostar left' f ::: left' fs
  {-# INLINE left' #-}

asCostar :: (Costar f d c -> Costar g b a) -> (f d -> c) -> g b -> a
asCostar f = runCostar . f . Costar
{-# INLINE asCostar #-}

-- }}}

-- Algebras {{{

type Algebras fs a = Matches fs a a

transAlgWith :: Functors fs => Subset fs gs -> Algebras fs (Fix gs)
transAlgWith = \case
  ØS      -> Void
  x :< xs -> Fix . In x ::: transAlgWith xs

transAlg :: (Functors fs, fs ⊆ gs) => Algebras fs (Fix gs)
transAlg = transAlgWith subset

-- }}}

-- Subset {{{

data Subset (fs :: [k]) (gs :: [k]) :: * where
  ØS   :: Subset Ø gs
  (:<) :: !(Index gs f)
       -> !(Subset fs gs)
       -> Subset (f :< fs) gs
infixr 5 :<

subNil :: Subset fs Ø -> fs :~: Ø
subNil = \case
  ØS     -> Refl
  x :< _ -> absurd $ ixNil x

class (fs :: [k]) ⊆ (gs :: [k]) where
  subset :: Subset fs gs
infix 4 ⊆

instance Ø ⊆ gs where
  subset = ØS

instance (f ∈ gs, fs ⊆ gs) => (f :< fs) ⊆ gs where
  subset = elemIndex :< subset

subIndex :: (fs ⊆ gs) => Index fs f -> Index gs f
subIndex = subIndexWith subset
{-# INLINE subIndex #-}

subIndexWith :: Subset fs gs -> Index fs f -> Index gs f
subIndexWith = \case
  ØS -> absurd . ixNil
  x :< xs -> \case
    IZ   -> x
    IS y -> subIndexWith xs y
{-# INLINE subIndexWith #-}

subRefl :: forall fs. Known Length fs => Subset fs fs
subRefl = go (known :: Length fs)
  where
  go :: Length gs -> Subset gs gs
  go = \case
    LZ   -> ØS
    LS l -> IZ :< subTail (go l)
  {-# INLINE go #-}
{-# INLINE subRefl #-}

subTrans :: Subset fs gs -> Subset gs hs -> Subset fs hs
subTrans = \case
  ØS      -> pure ØS
  x :< xs -> (:<) <$> flip subIndexWith x <*> subTrans xs
{-# INLINE subTrans #-}

subTail :: Subset fs gs -> Subset fs (g :< gs)
subTail = \case
  ØS      -> ØS
  x :< xs -> IS x :< subTail xs

-- }}}

fold :: Matches fs a a -> Fix fs -> a
fold m = match $ lmap (fold m) m

para :: Matches fs (a,Fix fs) a -> Fix fs -> a
para fs = fst . fold (fs &:& lmap snd (knownFunctors inns fs))

match :: Matches fs (Fix fs) b -> Fix fs -> b
match m (Fix (In x t)) = extractAt x m t

inns :: (Functors fs, Known Length fs) => Algebras fs (Fix fs)
inns = cotabulate Fix

knownFunctors :: ((Functors fs, Known Length fs) => r) -> Matches fs a b -> r
knownFunctors r = \case
  Void     -> r
  _ ::: fs -> knownFunctors r fs

