{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module LangDef where

newtype Fix f = In (f (Fix f))

data Val f = Val Int
data Add f = Add f f
data Mul f = Mul f f
data Lam f = Lam f
data Var f = Var Int
data Apl f = Apl f f
data Let f = Let f f
data Dub f = Dub f

data (f :+: g) e
  = L (f e)
  | R (g e)

instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (L a) = L $ fmap f a
    fmap f (R b) = R $ fmap f b

instance Functor Val where
    fmap f (Val v) = Val v

instance Functor Add where
    fmap f (Add a b) = Add (f a) (f b)

instance Functor Dub where
    fmap f (Dub a) = Dub (f a)

instance Functor Mul where
    fmap f (Mul a b) = Mul (f a) (f b)

instance Functor Lam where
    fmap f (Lam a) = Lam (f a)

instance Functor Var where
    fmap _ (Var i) = Var i

instance Functor Apl where
    fmap f (Apl a b) = Apl (f a) (f b)

instance Functor Let where
    fmap f (Let a b) = Let (f a) (f b)

fold :: Functor f => (f b -> b) -> Fix f -> b
fold f = go
    where go (In t) = f . fmap go $ t

class (Functor sub, Functor sup) => sub :<: sup where
    inj :: sub a -> sup a

instance (Functor f) => f :<: f where
    inj = id

instance (Functor f, Functor g) => f :<: (f :+: g) where
    inj = L

instance (Functor h, f :<: g) => f :<: (h :+: g) where
    inj = R . inj

inject :: (g :<: f) => g (Fix f) -> Fix f
inject = In . inj

val :: (Val :<: f) => Int -> Fix f
val n = inject (Val n)

add :: (Add :<: f) => Fix f -> Fix f -> Fix f
add x y = inject (Add x y)

mul :: (Mul :<: f) => Fix f -> Fix f -> Fix f
mul x y = inject (Mul x y)

dub :: (Dub :<: f) => Fix f -> Fix f
dub x = inject (Dub x)

lam :: (Lam :<: f) => Fix f -> Fix f
lam e = inject (Lam e)

var :: (Var :<: f) => Int -> Fix f
var e = inject (Var e)

apl :: (Apl :<: f) => Fix f -> Fix f -> Fix f
apl a b = inject (Apl a b)

lete :: (Let :<: f) => Fix f -> Fix f -> Fix f
lete a b = inject (Let a b)

