{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Lang where

data Double e = Double e
data Plus   e = Plus e e
data Times  e = Times e e
data Const  e = Const Int
data Lamb   e = Lamb e
data Apply  e = Apply e e
data Var    e = Var Int
data Let    e = Let e e
data Fix    e = Fix (e (Fix e))

data (f :+: g) e = Inl (f e) | Inr (g e)




-- This ugly type is inferred
-- desugarDouble
--   :: (Functor (OutOf (Minus t Lang.Double)),
--       Without t Lang.Double (Minus t Lang.Double),
--       Inj Plus (OutOf (Minus t Lang.Double))
--           (Into Plus (OutOf (Minus t Lang.Double)))) =>
--      Fix t -> Fix (OutOf (Minus t Lang.Double))
desugarDouble e =
  cases ((\(Double e) r ->
            Fix (inj (Plus (r e) (r e))))
         ? (const . Fix . fmap desugarDouble)) e

type L1 = (((Times :+: Lang.Double) :+: Const) :+: Plus)
type L2 = ((Times :+: Const) :+: Plus)

c1 :: Fix L1
c1 = Fix $ inj $ Const 2
c2 :: Fix L1
c2 = Fix $ inj $ Double c1
c3 :: Fix L1
c3 = Fix $ inj $ Plus c1 c2

-- Type is inferred
-- c2' :: Fix L2
c2' = desugarDouble c2 -- (+ 2 2)




(f <?> g) (Inl x) = f x
(f <?> g) (Inr x) = g x

instance (Functor f, Functor g) => Functor (f :+: g)
    where fmap f (Inl m) = Inl (fmap f m)
          fmap f (Inr m) = Inr (fmap f m)

instance (Show (f e), Show (g e)) => Show ((f :+: g) e) where
  show (Inl x) = show x -- "l" ++ show x
  show (Inr x) = show x -- "r" ++ show x

instance Show (e (Fix e)) => Show (Fix e) where
  show (Fix x) = show x

instance Show e => Show (Lang.Double e) where
  show (Double e) = "(double " ++ show e ++ ")"

instance Show e => Show (Plus e) where
  show (Plus x y) = "(+ " ++ show x ++ " " ++ show y ++ ")"

instance Show e => Show (Times e) where
  show (Times x y) = "(* "  ++ show x ++ " " ++ show y ++ ")"

instance Show (Const e) where
  show (Const n) = show n

instance Show e => Show (Lamb e) where
  show (Lamb e) = "(lambda " ++ show e ++ ")"

instance Show e => Show (Apply e) where
  show (Apply a b) = "(" ++ show a ++ " " ++ show b ++ ")"

instance Show e => Show (Var e) where
  show (Var i) = "(var " ++ show i ++ ")"

instance Functor Plus where
  fmap f (Plus m n) = Plus (f m) (f n)

instance Functor Times where
  fmap f (Times m n) = Times (f n) (f n)

instance Functor Const where
  fmap _ (Const x) = Const x

instance Functor Lang.Double where
  fmap f (Double x) = Double (f x)

instance Functor Let where
  fmap f (Let x y) = Let (f x) (f y)

instance Functor Lamb where
  fmap f (Lamb x) = Lamb (f x)

instance Functor Var where
  fmap _ (Var v) = Var v

instance Functor Apply where
  fmap f (Apply x y) = Apply (f x) (f y)


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

inj :: forall f g e. (Inj f g (Into f g)) => f e -> g e
inj = inj' (undefined :: Into f g)

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

(?) :: forall f g e r. Without f g (Minus f g) => (g e -> r) -> (OutOf (Minus f g) e -> r) -> f e -> r
m ? n = (??) m n (undefined :: Minus f g)

cases cs = f where f (Fix e) = cs e f
