{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
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

module Exp where

import Variants

import Control.Arrow
import Control.Monad
import Type.Family.Constraint
import Type.Family.List
import Data.Type.Index

data LamF r a where
  Var :: a -> LamF r a
  Lam :: (a -> r b) -> LamF r (a -> b)
  App :: r (a -> b) -> r a -> LamF r b

var :: (LamF ∈ fs) => a -> Rec fs a
var x = injRec $ Var x

lam :: (LamF ∈ fs) => (a -> Rec fs b) -> Rec fs (a -> b)
lam f = injRec $ Lam f

app :: (LamF ∈ fs) => Rec fs (a -> b) -> Rec fs a -> Rec fs b
app f a = injRec $ App f a

data LetF r a where
  Let :: r a -> (a -> r b) -> LetF r b

let_ :: (LetF ∈ fs) => Rec fs a -> (a -> Rec fs b) -> Rec fs b
let_ a f = injRec $ Let a f

data IfF r a where
  If :: r Bool -> r a -> r a -> IfF r a

if_ :: (IfF ∈ fs) => Rec fs Bool -> Rec fs a -> Rec fs a -> Rec fs a
if_ t c a = injRec $ If t c a

data NumF r a where
  Int    :: Int -> NumF r a
  Add    :: r Int -> r Int -> NumF r Int
  IsZero :: r Int -> NumF r Bool

int :: (NumF ∈ fs) => Int -> Rec fs Int
int i = injRec $ Int i

(.+) :: (NumF ∈ fs) => Rec fs Int -> Rec fs Int -> Rec fs Int
x .+ y = injRec $ Add x y
infixl 6 .+

isZero :: (NumF ∈ fs) => Rec fs Int -> Rec fs Bool
isZero a = injRec $ IsZero a

data DubF r a where
  Dub :: r Int -> DubF r Int

dub :: (DubF ∈ fs) => Rec fs Int -> Rec fs Int
dub a = injRec $ Dub a

type L1 = '[DubF,LamF,LetF,IfF,NumF]
type L2 = '[LamF,LetF,IfF,NumF]
type L3 = '[LamF,IfF,NumF]

type Exp1 = Rec L1
type Exp2 = Rec L2
type Exp3 = Rec L3

case_ :: Rec fs a -> (Rec fs a -> b) -> b
case_ t f = f t

(?) :: (f ∈ fs) => (f (Rec fs) a -> b) -> (Rec fs a -> b) -> Rec fs a -> b
(f ? g) t = case prjRec t of
  Just u -> f u
  _      -> g t
infixr 0 ?

recursive :: (HFoldables fs, f ∈ fs) => (f (Rec fs) a -> b) -> Rec fs a -> b
recursive f t = case prjRec t of
  Just u -> f u
  _      -> hfoldMap (recursive f) $ unroll t

{-
(?!) :: (HFoldables fs, f ∈ fs) => (f (Rec fs) a -> b) -> (forall g. HFoldable g => g (Rec fs) a -> b) -> Rec fs a -> b
(f ?! g) t = case prjRec t of
  Just u -> f u
  _      -> hfoldMap _ $ unroll t
infixr 0 ?!
-}

(&) :: a -> (a -> b) -> b
a & f = f a
infixr 0 &

desugarDub :: Exp1 a -> Exp2 a
desugarDub =
    (\(Dub x) -> desugarDub x .+ desugarDub x)
  ? (_)

{-

-- types {{{

type Var = String

data ExpF r
  = Var Var
  | Lit Lit
  | Less r r
  | If r r r
  | Lam Var r
  | App r r
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Lit
  = Int Integer
  | Bool Bool
  deriving (Eq,Ord,Show)

type Exp = Rec ExpF
type ExpA = Cofree ExpF

data LetF r
  = Let Var r r
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type LetExp = Rec (Sum ExpF LetF)

-- }}}

-- RemoveLet {{{

-- | Simple bottom-up transformation, using 

removeLet :: LetExp -> Exp
removeLet = cataRec $ \case
  InR t -> case t of
    Let x a b -> lam x b .@ a
  InL t -> Roll t

  -- }}}

-- sugar {{{

-- | Building closed terms

var :: Var -> Exp
var = Roll . Var

lit :: Lit -> Exp
lit = Roll . Lit

int :: Integer -> Exp
int = lit . Int

bool :: Bool -> Exp
bool = lit . Bool

(.<.) :: Exp -> Exp -> Exp
a .<. b = Roll $ Less a b
infix 4 .<.

ifte :: Exp -> Exp -> Exp -> Exp
ifte t c a = Roll $ If t c a

lam :: Var -> Exp -> Exp
lam x a = Roll $ Lam x a

(.@) :: Exp -> Exp -> Exp
a .@ b = Roll $ App a b
infixl 8 .@

-- }}}

-- typecheck {{{

data Type
  = IntT
  | BoolT
  | FunT Type Type
  | VarT Int
  deriving (Eq,Ord,Show)

data TCState = TCState
  { nextVar :: Int
  -- , memo    :: Map Exp (ExpA Type)
  }

freshTVar :: MonadState TCState m => m Type
freshTVar = do
  x <- gets nextVar
  modify $ \s -> s { nextVar = succ $ nextVar s }
  return $ VarT x

type TEnv = (Maps Var Type,Set (Type,Type))
type TC f a  = State TCState (f (Writer TEnv a))

annotateType :: Exp -> Maybe (ExpA Type) -- (ExpA Type,TEnv)
annotateType = uncurry solve . runWriter . (`evalStateT` initial) . typeCheck
  where
  initial :: TCState
  initial = TCState 0
  solve :: ExpA Type -> TEnv -> Maybe (ExpA Type)
  solve e env = traverse (\t -> (`subst` t) <$> solveConstraints env) e

type Subst = Map Int Type

solveConstraints :: TEnv -> Maybe Subst
solveConstraints (xs,cs) = foldl
  ( \ms (t1,t2) -> ms >>= \s -> (s <>) <$> unifyTypes (subst s t1) (subst s t2)
  ) (Just mempty)
  $ cs <> foldMaps choose2 xs

subst :: Subst -> Type -> Type
subst s = \case
  IntT     -> IntT
  BoolT    -> BoolT
  FunT a b -> FunT (subst s a) (subst s b)
  VarT x   -> fromMaybe (VarT x) $ Map.lookup x s

unifyTypes :: Type -> Type -> Maybe Subst
unifyTypes = curry $ \case
  (VarT x  ,b       ) -> return $ Map.singleton x b
  (a       ,VarT x  ) -> return $ Map.singleton x a
  (IntT    ,IntT    ) -> return mempty
  (BoolT   ,BoolT   ) -> return mempty
  (FunT a b,FunT c d) -> do
    s <- unifyTypes a c
    unifyTypes (subst s b) (subst s d)
  _                   -> mzero

typeCheck :: Exp -> StateT TCState (Writer TEnv) (ExpA Type)
typeCheck = (sequence .) $ annotate_ $ \case
  Var x    -> do
    tx <- freshTVar
    tell (singleton x tx,mempty)
    return tx
  Lit l    -> case l of
    Int i  -> return IntT
    Bool b -> return BoolT
  Less a b -> do
    tx <- freshTVar
    t1 <- a
    t2 <- b
    tell (mempty,Set.fromList [(t1,IntT),(t2,IntT),(tx,BoolT)])
    return tx
  If t c a -> do
    tx <- freshTVar
    t1 <- t
    t2 <- c
    t3 <- a
    tell (mempty,Set.fromList [(t1,BoolT),(t2,tx),(t3,tx)])
    return tx
  Lam x a -> do
    [tx,ty] <- replicateM 2 freshTVar
    (t1,xs) <- listens (lookups x . fst) a
    tell (mempty,Set.insert (ty,t1) $ Set.map ((,) tx) xs)
    return $ FunT tx ty
  App a b -> do
    [tx,ty] <- replicateM 2 freshTVar
    t1 <- a
    t2 <- b
    tell (mempty,Set.fromList [(t1,FunT tx ty),(t2,tx)])
    return ty

-- }}}

-- evaluate {{{

data Val
  = IntV Integer
  | BoolV Bool
  | FunV Env Var Exp
  deriving (Eq,Ord,Show)

type Env = Map Var Val
type Eval = ReaderT Env Maybe

annotateVal :: Exp -> ExpA (Maybe Val)
annotateVal = fmap (`runReaderT` mempty) . evaluate

evaluate :: Exp -> ExpA (Eval Val)
evaluate = annotate $ \case
  Var x    -> asks (Map.lookup x) >>= \case
    Just v -> return v
    _      -> mzero
  Lit l    -> case l of
    Int i  -> return $ IntV i
    Bool b -> return $ BoolV b
  Less (_,a) (_,b) -> do
    v1 <- a
    v2 <- b
    case (v1,v2) of
      (IntV x, IntV y) -> return $ BoolV $ x < y
      _                -> mzero
  If (_,t) (_,c) (_,a) -> do
    v <- t
    case v of
      BoolV b -> if b then c else a
      _       -> mzero
  Lam x (a,_)  -> do
    env <- ask
    return $ FunV env x a
  App (_,a) (_,b)  -> do
    v1 <- a
    v2 <- b
    case v1 of
      FunV env x c -> extract $ fmap (local $ const $ Map.insert x v2 env) $ evaluate c
      _            -> mzero

-- }}}

-- Maps {{{

newtype Maps k a = Maps
  { getMaps :: Map k (Set a)
  } deriving (Eq,Ord,Show)

instance (Ord k, Ord a) => Monoid (Maps k a) where
  mempty = Maps mempty
  Maps m1 `mappend` Maps m2 = Maps $ {- Map.filter (not . null) $ -} Map.unionWith (<>) m1 m2

maps :: Ord k => k -> Set a -> Maps k a
maps k as = Maps $ Map.singleton k as

singleton :: (Ord k, Ord a) => k -> a -> Maps k a
singleton k a = maps k $ Set.singleton a

insertAll :: (Ord k, Ord a) => k -> Set a -> Maps k a -> Maps k a
insertAll k as = mappend $ maps k as

deleteAll :: Ord k => k -> Maps k a -> Maps k a
deleteAll k = Maps . Map.delete k . getMaps

unionWith :: Ord k => (Set a -> Set a -> Set a) -> Maps k a -> Maps k a -> Maps k a
unionWith f m1 m2 = Maps $ Map.unionWith f (getMaps m1) (getMaps m2)

intersectionWith :: Ord k => (Set a -> Set a -> Set a) -> Maps k a -> Maps k a -> Maps k a
intersectionWith f m1 m2 = Maps $ Map.intersectionWith f (getMaps m1) (getMaps m2)

adjustAll :: Ord k => k -> (Set a -> Set a) -> Maps k a -> Maps k a
adjustAll k f = Maps . Map.adjust f k . getMaps

updateAll :: Ord k => k -> (Set a -> Maybe (Set a)) -> Maps k a -> Maps k a
updateAll k f = Maps . Map.update f k . getMaps

alterAll :: Ord k => k -> (Maybe (Set a) -> Maybe (Set a)) -> Maps k a -> Maps k a
alterAll k f = Maps . Map.alter f k . getMaps

inserts :: (Ord k, Ord a) => k -> a -> Maps k a -> Maps k a
inserts k a = mappend $ singleton k a

deletes :: (Ord k, Ord a) => k -> a -> Maps k a -> Maps k a
deletes k a = Maps . Map.update (nonEmptySet . Set.delete a) k . getMaps

updates :: (Ord k, Ord a) => k -> (a -> Maybe a) -> Maps k a -> Maps k a
updates k f = updateAll k $ nonEmptySet . maybeSet f

adjusts :: (Ord k, Ord a) => k -> (a -> a) -> Maps k a -> Maps k a
adjusts k f = updateAll k $ nonEmptySet . Set.map f

lookups :: (Ord k, Ord a) => k -> Maps k a -> Set a
lookups k = fromMaybe mempty . Map.lookup k . getMaps

partitions :: (Ord k, Ord a) => (a -> Bool) -> Maps k a -> (Maps k a,Maps k a)
partitions f = unzips . fmap (Set.partition f) . getMaps
  where
  unzips = Map.foldMapWithKey $ \k (y,n) -> -- (maps k y,maps k n)
    let
    y' = if null y then mempty else maps k y
    n' = if null n then mempty else maps k n
    in (y',n')

foldMaps :: Monoid m => (Set a -> m) -> Maps k a -> m
foldMaps f = foldMap f . getMaps

-- }}}

-- Helpers {{{

nonEmptySet :: Set a -> Maybe (Set a)
nonEmptySet as = as <$ guard (not $ null as)

maybeSet :: (Foldable f, Ord b) => (a -> Maybe b) -> f a -> Set b
maybeSet f = Set.fromList . mapMaybe f . F.toList

choose2 :: Ord a => Set a -> Set (a,a)
choose2 as = snd
  $ foldr
  ( \a (s,ps) -> let
    s' = Set.delete a s
    in (s',Set.map ((,) a) s' <> ps)
  ) (as,mempty) as

-- }}}
-}

