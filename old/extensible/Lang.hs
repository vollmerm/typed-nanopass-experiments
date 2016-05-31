{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Lang where

import GHC.Exts (Constraint)
import Data.Function (fix)

data Term  e = Term (e (Term e))
data (f :+: g) e = Inl (f e) | Inr (g e)
  deriving (Eq,Ord,Functor,Foldable,Traversable)
infixl 6 :+:

instance Show (f (Term f)) => Show (Term f) where
  showsPrec d (Term t) = showsPrec d t

instance (Show (f a), Show (g a)) => Show ((f :+: g) a) where
  showsPrec d = \case
    Inl a -> showsPrec d a
    Inr b -> showsPrec d b

data Dub   e = Dub   e   deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Plus  e = Plus  e e deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Times e = Times e e deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Const e = Const Int deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Lamb  e = Lamb  e   deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Apply e = Apply e e deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Var   e = Var   Int deriving (Eq,Ord,Show,Functor,Foldable,Traversable)
data Let   e = Let   e e deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Member f g = Inj f g (Into f g)
type Remove g f h = (Without f g (Minus f g), h ~ OutOf (Minus f g))
type f \\ g = OutOf (Minus f g)
type RequireIn g f = (Without f g (Minus f g), Member g f)

-- $ (\(Dub e1) r1 -> casesOf e1
--   $ (\(Plus e2 e3) r2 ->
--     r1 e2 .+ r1 e3
-- desugarDub ::
--   ( Remove Plus u v
--   , Member Plus   v
--   , Remove Dub  u v
--   , Functor       v
--   ) => Term u -> Term v

-- $ (\(Dub e1) r1 -> casesOf (r1 e1)
--   $ (\(Plus e2 e3) r2 ->
--     r2 e2 .+ r2 e3
-- desugarDub ::
--   ( Remove Dub  u v
--   , Remove Plus v v
--   , Functor v
--   , Member Plus v
--   ) => Term u -> Term v
-- r1 e2 .+ r2 e3
--
-- desugarDub :: forall u v w. 
--   ( Remove Dub u v
--   , Functor v
--   , Remove Plus v w
--   , Member Plus v
--   ) => Term u -> Term v

{-
desugarDub :: forall u v.
  ( Remove Dub u v
  , RequireIn Plus v
  , Functor v
  ) => Term u -> Term v
desugarDub e = casesOf e
  $ (\(Dub e1) r1 -> casesOf (r1 e1)
    $ (\(Plus e2 e3) r2 ->
      r2 e2 .+ r2 e3
      -- r2 e2 .+ r2 e3
      -- r1 e2 .+ r2 e3
      )
    ? _
    -- r e .+ r e
    )
  ? everywhere -- (undefined :: v (Term u) -> (Term u -> Term v) -> Term v)
-}

(.+) :: Member Plus e => Term e -> Term e -> Term e
a .+ b = term $ Plus a b
infixl 6 .+

type L1 = Times :+: Dub :+: Const :+: Plus
type L2 = Times :+: Const :+: Plus

c1 :: Term L1
c1 = term $ Const 2
c2 :: Term L1
c2 = term $ Dub c1
c3 :: Term L1
c3 = term $ Plus c1 c2

-- Type is inferred
-- c2' :: Term L2
-- c2' = desugarDub c2 -- (+ 2 2)

type L3 = Apply :+: Var :+: Lamb :+: Let :+: Times :+: Const :+: Plus
type L4 = Apply :+: Var :+: Lamb :+: Times :+: Const :+: Plus

c4 :: Term L3
c4 = term $ Let (term $ Const 1) (term $ Var 0)

c4' = desugarLet c4 -- ((lamba (var 0)) 1)

-- desugarLet
--   :: (Functor (OutOf (Minus t Let)), Without t Let (Minus t Let),
--       Inj Apply (OutOf (Minus t Let)) (Into Apply (OutOf (Minus t Let))),
--       Inj
--         Lamb (OutOf (Minus t Let)) (Into Lamb (OutOf (Minus t Let)))) =>
--      Term t -> Term (OutOf (Minus t Let))
desugarLet =
  cases $ \r ->
      (\(Let e1 e2) ->
            term $ Apply (term $ Lamb (r e2)) (r e1))
    ? (const . Term . fmap desugarLet)

term :: Member f g => f (Term g) -> Term g
term = Term . inj

(?) :: forall f g h e r. Remove g f h => (g e -> r) -> (h e -> r) -> f e -> r
m ? n = (??) m n (undefined :: Minus f g)
infixr 0 ?

cases :: ((Term u -> t) -> u (Term u) -> t) -> Term u -> t
cases cs = fix $ \f (Term e) -> cs f e

{-
casesOf :: Term u -> ((Term u -> t) -> u (Term u) -> t) -> t
casesOf e cs = cases cs e
-}

{-
casesOf :: Term u -> ((Term u -> t) -> u (Term u) -> t) -> t
casesOf t
-}

everywhere :: Functor t => t a -> (a -> Term t) -> Term t
everywhere e f = Term $ f <$> e

-- Machinery {{{

(f <?> g) (Inl x) = f x
(f <?> g) (Inr x) = g x

data Yep
data Nope

type family IsIn f g where
  IsIn f f         = Yep
  IsIn (f :+: f') (g :+: g') = Or (Or (IsIn (f :+: f') g) (IsIn (f :+: f') g')) (And (IsIn f (g :+: g')) (IsIn f' (g :+: g')))
  IsIn f (g :+: h) = Or (IsIn f g) (IsIn f h)
  IsIn f g         = Nope

type family Or b c where
  Or Nope Nope = Nope
  Or b c       = Yep

type family And b c  where
  And Yep Yep = Yep
  And b c     = Nope

data L x
data R x
data S x y
data End



type family Into f g where
  Into f f         = End
  Into (f :+: f') (g :+: g') = Ifii (Into (f :+: f') g) (IsIn (f :+: f') g')
                                    (Into (f :+: f') g') (IsIn (f :+: f') g)
                                    (Into f (g :+: g')) (Into f' (g :+: g'))
  Into f (g :+: h) = Ifi (Into f g) (IsIn f h) (Into f h) (IsIn f g)
  Into f g         = Nope

type family Ifi p a q b where
  Ifi Nope a Nope b = Nope
  Ifi Nope a q Nope = R q
  Ifi p Nope q b    = L p
  Ifi p a q b       = Nope

type family Ifii p a q b s r where
  Ifii Nope a Nope b Nope r = Nope
  Ifii Nope a Nope b s Nope = Nope
  Ifii Nope a Nope b s r    = S s r
  Ifii Nope a q Nope s r    = R q
  Ifii p Nope q b s r       = L p
  Ifii p a q b s r          = Nope

inj :: forall f g e. Member f g => f e -> g e
inj = inj' (undefined :: Into f g)

class Inj f g p where
  inj' :: p -> f e -> g e

instance Inj f f End where
  inj' _ = id

instance Inj f g p => Inj f (g :+: h) (L p) where
  inj' (_ :: L p) = Inl . inj' (undefined :: p)

instance Inj f h p => Inj f (g :+: h) (R p) where
  inj' (_ :: R p)  = Inr . inj' (undefined :: p)

instance (Inj f h s, Inj g h r) => Inj (f :+: g) h (S s r) where
  inj' (_ :: S s r) = inj' (undefined :: s) <?> inj' (undefined :: r)

data Onl (x :: * -> *)
data Onr (x :: * -> *)
data Le (x :: * -> *) p
data Ri (x :: * -> *) p

type family Minus f g where
  Minus (f :+: g) f = Onl g
  Minus (f :+: g) g = Onr f
  Minus (f :+: g) h = Ifm g (Minus f h) (IsIn h g) f (Minus g h) (IsIn h f)

type family Ifm g p a f q b where
  Ifm g Nope a f Nope b = Nope
  Ifm g Nope a f q Nope = Ri f q
  Ifm g p Nope f q b    = Le g p

type family OutOf p where
  OutOf (Onl x) = x
  OutOf (Onr x) = x
  OutOf (Le f p) = OutOf p :+: f
  OutOf (Ri f p) = f :+: OutOf p

class Without f g p where
  (??) :: (g e -> r) -> (OutOf p e -> r) -> p -> f e -> r

instance Without (f :+: g) f (Onl g) where
  (m ?? n) _ (Inl x) = m x
  (m ?? n) _ (Inr x) = n x

instance Without (f :+: g) g (Onr f) where
  (m ?? n) _ (Inl x) = n x
  (m ?? n) _ (Inr x) = m x

instance Without f h p => Without (f :+: g) h (Le g p) where
  (m ?? n) (_ :: Le g p) (Inl x) = (m ?? (n . Inl)) (undefined :: p) x
  (m ?? n) (_ :: Le g p) (Inr x) = n (Inr x)

instance Without g h p => Without (f :+: g) h (Ri f p) where
  (m ?? n) (_ :: Ri f p) (Inl x) = n (Inl x)
  (m ?? n) (_ :: Ri f p) (Inr x) = (m ?? (n . Inr)) (undefined :: p) x

-- }}}

