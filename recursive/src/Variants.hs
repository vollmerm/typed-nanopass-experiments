{-# LANGUAGE AllowAmbiguousTypes #-}
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

import Control.Arrow ((>>>),right)
import Control.Monad (MonadPlus(..))
import Type.Class.Higher
import Type.Class.Witness
import Type.Family.Constraint (type Constraint, ØC)
import Type.Family.List
import Data.Type.Index (Index(..), type (∈), Elem(..), ixNil)

every1 :: ListC (c <$> as) => Index as a -> Wit (c a)
every1 = \case
  IZ   -> Wit
  IS x -> every1 x

allOp :: AllOp c fs x => Index fs f -> Wit (c (f x))
allOp = \case
  IZ   -> Wit
  IS x -> allOp x

allOp2 :: AllOp2 c fs x y => Index fs f -> Wit (c (f x y))
allOp2 = \case
  IZ   -> Wit
  IS x -> allOp2 x

type All    c as     = ListC (c <$> as)
type AllOp  c as x   = ListC (c <$> as <&> x)
type AllOp2 c as x y = ListC (c <$> as <&> x <&> y)

type Functors1 fs = All Functor1 fs

data Match (fs :: [(* -> *) -> * -> *]) (r :: * -> *) :: * -> * -> * where
  Total :: Match Ø r a b
  Elim  :: Without f fs gs
        => (f r a -> b)
        -> Match gs r a b
        -> Match fs r a b
  Match :: (f ∈ fs)
        => (f r a -> b)
        -> Match fs r a b
        -> Match fs r a b
  Pass :: (All Functor1 fs, fs ⊆ gs)
       => Match fs (Rec fs) a (Rec gs a)
  Else :: (Variants fs r a -> b)
       -> Match fs r a b

data MatchRec (fs :: [(* -> *) -> * -> *]) (gs :: [(* -> *) -> * -> *]) :: * where
  PassRec  :: (fs ⊆ gs)
           => MatchRec fs gs
  TotalRec :: MatchRec Ø gs
  ElimRec  :: Without f fs gs
           => (forall x. f (Rec hs) x -> Rec hs x)
           -> MatchRec gs hs
           -> MatchRec fs hs
  MatchRec :: (f ∈ fs)
           => (forall x. f (Rec gs) x -> Rec gs x)
           -> MatchRec fs gs
           -> MatchRec fs gs
  ElseRec  :: (forall x. Variants fs (Rec gs) x -> Rec gs x)
           -> MatchRec fs gs

{-
data Subset :: [k] -> [k] -> * where
  ØS   :: Subset bs bs
  (:∈) :: !(Rem a bs cs)
       -> !(Subset as cs)
       -> Subset as bs
  (:∋) :: !(Index bs a)
       -> !(Subset as bs)
       -> Subset (a :< as) bs
infixr 5 :∈
infixr 5 :∋
-}

data Rem :: k -> [k] -> [k] -> * where
  RZ :: Rem a (a :< as) as
  RS :: !(Rem a as bs)
     -> Rem a (b :< as) (b :< bs)

remWit :: forall c a as bs. Rem a as bs -> WitAll c as -> WitAll c bs
remWit = \case
  RZ   -> \(WitAll Wit) -> WitAll Wit
  RS r -> go r
  where
  go :: forall x y xs ys. Rem x xs ys -> WitAll c (y :< xs) -> WitAll c (y :< ys)
  go r (WitAll Wit) = case remWit r (WitAll Wit :: WitAll c xs) of
    WitAll Wit -> WitAll Wit

decompIx :: Rem a as bs -> Index as b -> Either (a :~: b) (Index bs b)
decompIx = \case
  RZ   -> \case
    IZ   -> Left Refl
    IS x -> Right x
  RS r -> \case
    IZ   -> Right IZ
    IS x -> right IS $ decompIx r x

liftIx :: Rem a as bs -> Index bs b -> Index as b
liftIx = \case
  RZ   -> IS
  RS r -> \case
    IZ   -> IZ
    IS x -> IS $ liftIx r x

{-
remSubset :: Rem a as bs -> Subset bs as
remSubset = \case
  RZ   -> RZ :∈ ØS
  RS r -> IZ :∋ RZ :∈ remSubset r
-}

{-
subsetIx :: Subset as bs -> Index as a -> Index bs a
subsetIx = \case
  ØS     -> id
  r :∈ s -> liftIx r . subsetIx s
  x :∋ s -> \case
    IZ   -> x
    IS y -> subsetIx s y
-}

class (a ∈ as) => Without (a :: k) (as :: [k]) (bs :: [k]) | a as -> bs where
  without :: Rem a as bs

instance {-# OVERLAPPING #-} (bs ~ as) => Without a (a :< as) bs where
  without = RZ

instance {-# OVERLAPPABLE #-} (cs ~ (b :< bs), Without a as bs) => Without a (b :< as) cs where
  without = RS without

data Diff :: [k] -> [k] -> [k] -> * where
  ØD   :: Diff Ø bs bs
  (:-) :: !(Rem a bs cs)
       -> !(Diff as cs ds)
       -> Diff (a :< as) bs ds
infixr 5 :-

class WithoutAll (as :: [k]) (bs :: [k]) (cs :: [k]) | as bs -> cs where
  withoutAll :: Diff as bs cs

instance (cs ~ bs) => WithoutAll Ø bs cs where
  withoutAll = ØD

instance (Without a bs cs, WithoutAll as cs ds) => WithoutAll (a :< as) bs ds where
  withoutAll = without :- withoutAll

elimVariantBy :: Rem f fs gs
              -> (f r a -> b)
              -> (Variants gs r a -> b)
              -> Variants fs r a -> b
elimVariantBy = \case
  RZ   -> \f g -> \case
    L a -> f a
    R b -> g b
  RS r -> \f g -> let
    h = elimVariantBy r f (g . R)
    in \case
    L a -> g $ L a
    R b -> h b

elimVariant :: Without f fs gs
            => (f r a -> b)
            -> (Variants gs r a -> b)
            -> Variants fs r a -> b
elimVariant = elimVariantBy without

elimVariant1By :: Rem f fs gs
               -> (forall x. f r x -> r x)
               -> (forall x. Variants gs r x -> r x)
               -> Variants fs r a -> r a
elimVariant1By r f g = case r of
  RZ    -> \case
    L a -> f a
    R b -> g b
  RS r' -> \case
    L a -> g $ L a
    R b -> elimVariant1By r' f (g . R) b

elimVariant1 :: Without f fs gs
               => (forall x. f r x -> r x)
               -> (forall x. Variants gs r x -> r x)
               -> Variants fs r a -> r a
elimVariant1 = elimVariant1By without

type family Remove (a :: k) (as :: [k]) :: [k] where
  Remove a (a :< as) = as
  Remove a (b :< as) = b :< Remove a as

match :: Match fs (Rec fs) a b -> Rec fs a -> b
match c = match' c . unroll

match' :: Match fs r a b -> Variants fs r a -> b
match' = \case
  Total      -> emptyVariants
  Elim  f fs -> elimVariant f $ match' fs
  Match f fs -> replaceAt f (match' fs) elemIndex
  Pass       -> Roll . variants (fix1 $ \rec -> boilerplate rec)
  Else f     -> f

matchRec :: All Functor1 fs => MatchRec fs gs -> Rec fs a -> Rec gs a
matchRec c = unroll >>> map1 (matchRec c) >>> matchRec' c

data WitAll (c :: k -> Constraint) :: [k] -> * where
  WitAll :: { getWitAll :: Wit (All c as) }
         -> WitAll c as

matchRec' :: forall fs gs a. All Functor1 fs => MatchRec fs gs -> Variants fs (Rec gs) a -> Rec gs a
matchRec' = \case
  PassRec       -> Roll . variants id
  TotalRec      -> emptyVariants
  ElimRec (f :: forall x. f (Rec gs) x -> Rec gs x) (fs :: MatchRec hs gs) ->
    elimVariant f $ matchRec' fs \\ getWitAll w'
    where
    w :: WitAll Functor1 fs
    w = WitAll Wit
    w' :: WitAll Functor1 hs
    w' = remWit (without :: Rem f fs hs) w
   -- (f :: forall x. f  fs -> case remWit _ (Wit :: Wit (All Functor1 fs)) of
   -- Wit -> elimVariant f $ matchRec' fs
  MatchRec f fs -> replaceAt1 f (matchRec' fs) elemIndex
  ElseRec  f    -> f

foldRec1 :: All Functor1 fs => (forall f x. Index fs f -> f r x -> r x) -> Rec fs a -> r a
foldRec1 f = foldVariants1 f . map1 (foldRec1 f) . unroll

foldVariants1 :: (forall f x. Index fs f -> f r x -> s x) -> Variants fs r a -> s a
foldVariants1 f = \case
  L a -> f IZ a
  R b -> foldVariants1 (f . IS) b

replace :: (f ∈ fs) => (f r a -> b) -> (Variants fs r a -> b) -> Variants fs r a -> b
replace f g = replaceAt f g elemIndex

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

{-
type as ⊆ bs = All (Elem bs) as
-}

data Subset :: [k] -> [k] -> * where
  ØS   :: Subset as as
  (:+) :: !(Rem a bs cs)
       -> !(Subset as cs)
       -> Subset as bs
infixr 5 :+

class (as :: [k]) ⊆ (bs :: [k]) where
  subset   :: Subset as bs
  subsetIx :: Index as x -> Index bs x
infix 4 ⊆

instance {-# OVERLAPPING #-} as ⊆ as where
  subset   = ØS
  subsetIx = id

instance {-# OVERLAPPABLE #-} (Without a bs cs, as ⊆ cs) => as ⊆ bs where
  subset   = (without :: Rem a bs cs) :+ subset
  subsetIx = liftIx (without :: Rem a bs cs) . (subsetIx :: forall x. Index as x -> Index cs x)

{-
instance Ø ⊆ bs where
  subset = ØS

instance (a ∈ bs, as ⊆ bs) => (a :< as) ⊆ bs where
  subset = elemIndex :+ subset
-}

variant :: (Functor1 f, f ∈ fs) => (forall x. r x -> s x) -> f r a -> Variants fs s a
variant f = inj . map1 f

variants :: (All Functor1 fs, fs ⊆ gs) => (forall x. r x -> s x) -> Variants fs r a -> Variants gs s a
variants = variantsBy subset

variantsBy :: All Functor1 fs => Subset fs gs -> (forall x. r x -> s x) -> Variants fs r a -> Variants gs s a
variantsBy s f = undefined
  -- case s of
  -- ØS      -> emptyVariants
  -- x :+ s' -> \case
  --   L a -> injBy x $ map1 f a
  --   R b -> variantsBy s' f b

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
    El y b -> injBy y b
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
      El y b -> injBy y b
    ) <$> f IZ a
  R b -> itraverseVariants (f . IS) b

inj :: (f ∈ fs) => f r a -> Variants fs r a
inj = injBy elemIndex

prj :: (f ∈ fs, MonadPlus m) => Variants fs r a -> m (f r a)
prj = prjBy elemIndex

injBy :: Index fs f -> f r a -> Variants fs r a
injBy = \case
  IZ   -> L
  IS x -> R . injBy x

prjBy :: MonadPlus m => Index fs f -> Variants fs r a -> m (f r a)
prjBy = \case
  IZ   -> \case
    L a -> return a
    _   -> mzero
  IS x -> \case
    R a -> prjBy x a
    _   -> mzero

injSubBy :: (forall f. Index fs f -> Index gs f) -> Variants fs r a -> Variants gs r a
injSubBy f = \case
  L a -> injBy (f IZ) a
  R b -> injSubBy (f . IS) b

prjSubBy :: MonadPlus m => (forall f. Index gs f -> m (Index fs f)) -> Variants gs r a -> m (Variants fs r a)
prjSubBy f = \case
  L a -> do
    x <- f IZ
    return $ injBy x a
  R b -> prjSubBy (f . IS) b

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

{-
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
-}

