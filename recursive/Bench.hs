{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ConstraintKinds #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

-- module Exp where

import Variants

import Control.Monad.Fix
import Type.Class.Higher (Functor1(..),Foldable1(..))
import Data.Type.Index (type (∈),Index(..))
import Data.Functor.Constant
import Data.Function (fix)
import Data.Typeable
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Criterion.Main
import GHC.Generics (Generic)
import Control.DeepSeq


-- This generates a series of nested `let` expressions, desugars all of them,
-- and converts the resulting expression to a string.
main :: IO ()
main = defaultMain [
        bgroup "generic"
        [ bench "10"  $ nf forceAll $ genericBench 10
        , bench "50"  $ nf forceAll $ genericBench 50
        , bench "100"  $ nf forceAll $ genericBench 100
        , bench "500"  $ nf forceAll $ genericBench 500
        , bench "1000" $ nf forceAll $ genericBench 1000
        ]
       , bgroup "oneADT"
        [ bench "10"  $ nf oneBench 10
        , bench "50"  $ nf oneBench 50
        , bench "100"  $ nf oneBench 100
        , bench "500"  $ nf oneBench 500
        , bench "1000" $ nf oneBench 1000
        ]        
       ]

-- forceAll = undefined

buildExpr :: Int -> Exp2 Int
buildExpr 0 = Let "x" (Int 0) (Var "x")
buildExpr i = Let "z" (Int i) (buildExpr (i - 1))

genericBench i = genericBench' i

genericBench' :: Int -> Exp3 Int
genericBench' i = desugarLet $ buildExpr i

data OneADT = OLamb String OneADT | OLet String OneADT OneADT |
              OApply OneADT OneADT | ODub OneADT | OAdd OneADT OneADT |
              OInt Int | OVar String
              deriving (Show, Generic, NFData)
                       
-- renderOne e = (renderOne' e) ""

-- renderOne' :: OneADT -> ShowS
-- renderOne' (OLamb v e) = showParen True
--                        $ showChar '\\'
--                        . showString v
--                        . showString " -> "
--                        . renderOne' e
-- renderOne' (OLet v e1 e2) = showParen True
--                          $ showString "let "
--                          . showString v
--                          . showString " = "
--                          . renderOne' e1
--                          . showString " in "
--                          . renderOne' e2
-- renderOne' (OApply e1 e2) = showParen True
--                          $ renderOne' e1
--                          . showChar ' '
--                          . renderOne' e2
-- renderOne' (ODub e) = showParen True
--                    $ showString "dub "
--                    . renderOne' e
-- renderOne' (OInt i) = shows i
-- renderOne' (OVar v) = shows v

buildOneADT :: Int -> OneADT
buildOneADT 0 = OLet "x" (OInt 0) (OVar "x")
buildOneADT i = OLet "z" (OInt i) (buildOneADT (i - 1))

oneBench :: Int -> OneADT
oneBench i = oneDesugarLet $ buildOneADT i

oneDesugarDub :: OneADT -> OneADT
oneDesugarDub (OLamb v e) = OLamb v (oneDesugarDub e)
oneDesugarDub (OLet v e1 e2) = OLet v (oneDesugarDub e1) (oneDesugarDub e2)
oneDesugarDub (OApply e1 e2) = OApply (oneDesugarDub e1) (oneDesugarDub e2)
oneDesugarDub (ODub e) = let e' = (oneDesugarDub e) in OAdd e e
oneDesugarDub (OAdd e1 e2) = OAdd (oneDesugarDub e1) (oneDesugarDub e2)
oneDesugarDub (OInt i) = OInt i
oneDesugarDub (OVar s) = OVar s

oneDesugarLet :: OneADT -> OneADT
oneDesugarLet (OLamb v e) = OLamb v (oneDesugarLet e)
oneDesugarLet (OLet v e1 e2) = OApply (OLamb v (oneDesugarLet e2)) (oneDesugarLet e1)
oneDesugarLet (OApply e1 e2) = OApply (oneDesugarLet e1) (oneDesugarLet e2)
oneDesugarLet (ODub e) = error "Impossible"
oneDesugarLet (OAdd e1 e2) = OAdd (oneDesugarDub e1) (oneDesugarDub e2)
oneDesugarLet (OInt i) = OInt i
oneDesugarLet (OVar s) = OVar s
       
desugarDub ::
  ( Functors1 l_1
  , Without DubF l_1 l_2
  , NumF ∈ l_2
  ) => Rec l_1 a -> Rec l_2 a
desugarDub = everywhere
  $ ElimRec ? \case
    DUB x -> Add x x
  $ PassRec

desugarLet ::
  ( Functors1 l_1
  , Without LetF l_1 l_2
  , LamF ∈ l_2
  ) => Rec l_1 a -> Rec l_2 a
desugarLet = everywhere
  $ ElimRec ? \case
    LET x a b -> App (Lam x b) a
  $ PassRec

desugarDubLet ::
  ( Functors1 l_1
  , Without DubF l_1 l_2
  , Without LetF l_2 l_3
  , LamF ∈ l_3
  , NumF ∈ l_3
  ) => Rec l_1 a -> Rec l_3 a
-- desugarDubLet :: Exp1 a -> Exp3 a
desugarDubLet = everywhere
  $ ElimRec ? \case
    DUB x -> Add x x
  $ ElimRec ? \case
    LET x a b -> App (Lam x b) a
  $ PassRec

swapAdd ::
  ( All Functor1 l
  , NumF ∈ l
  ) => Rec l a -> Rec l a
swapAdd = everywhere
  $ MatchRec ? \case
    ADD x y -> Add y x
  $ PassRec

-- data Unit a = Unit deriving (Show)

-- instance Functor Unit where
--     fmap _ _    = Unit

class Forced (f :: (* -> *) -> * -> *) where
  forced :: f (Constant ()) a -> Constant () a

class Render (f :: (* -> *) -> * -> *) where
  render :: f (Constant ShowS) a -> Constant ShowS a

forceAll :: (All Forced fs, All Functor1 fs) => Rec fs a -> ()
forceAll = getConstant . byClass (undefined :: prx Forced) forced

renderAll :: (All Render fs, All Functor1 fs) => Rec fs a -> String
renderAll = ($ "") . getConstant . byClass (undefined :: prx Render) render

byClass :: forall prx c fs r a. (All c fs, All Functor1 fs) => prx c -> (forall f x. c f => f r x -> r x) -> Rec fs a -> r a
byClass p f = go . map1 (byClass p f) . unroll
  where
  go :: forall gs x. All c gs => Variants gs r x -> r x
  go = \case
    L a -> f a
    R b -> go b

-- data Val :: * where
--   Val :: Typeable a => a -> Val

-- data Eval :: (* -> *) -> * -> * where
--   EV :: ((forall x. Typeable x => String -> Maybe x) -> a) -> Eval r a

-- pattern Ev f <- (prjRec -> Just (EV f))
--   where
--   Ev f = injRec $ EV f

-- eval :: Exp1 a -> a
-- eval e = case eval' e of
--   Ev a -> a $ const Nothing

-- eval' :: Exp1 a -> Rec '[Eval] a
-- eval' = everywhere
--   $ ElimRec ? \case
--     LAM x (Ev b)      -> Ev $ \k a -> b $ \y -> if x == y then cast a else k y
--     APP (Ev a) (Ev b) -> Ev $ \k -> a k (b k)
--     VAR x             -> Ev $ \k -> case k x of
--       Just v -> v
--       _      -> error $ "unbound variable: " ++ x
--   $ ElimRec ? \case
--     DUB (Ev x)        -> Ev $ \k -> x k + x k
--   $ ElimRec ? \case
--     IF (Ev t) (Ev c) (Ev a) -> Ev $ \k -> if t k then c k else a k
--   $ ElimRec ? \case
--     LET x (Ev a) (Ev b) -> Ev $ \k -> b $ \y -> if x == y then cast (a k) else k y
--   $ ElimRec ? \case
--     INT i             -> Ev $ \_ -> i
--     ADD (Ev x) (Ev y) -> Ev $ \k -> x k + y k
--     ISZERO (Ev x)     -> Ev $ \k -> x k == 0
--   $ TotalRec

-- subst ::
--   ( LamF ∈ l
--   , Typeable b
--   ) => String -> Rec l b
--     -> Rec l a -> Rec l a
-- subst x v = match
--   $ Match ?? \case
--     VAR y
--       | x == y
--       , Just v' <- gcast v -> v'
--       | otherwise -> Var y
--   $ Pass

-- beta ::
--   ( All Functor1 l
--   , LamF ∈ l
--   ) => Rec l a -> Rec l a
-- beta = everywhere
--   $ MatchRec ? \case
--     APP (Lam x b) a -> subst x a b
--     e               -> injRec e
--   $ PassRec

-- freeVars ::
--   ( LamF ∈ l
--   , All HFoldable l
--   ) => Rec l a -> Set String
-- freeVars = match
--   $ Match ?? \case
--     VAR x   -> Set.singleton x
--     LAM x b -> Set.delete x (freeVars b)
--     APP a b -> Set.union (freeVars a) (freeVars b)
--   $ Else $ hfoldMap freeVars

{-
eta ::
  ( All HFoldable l
  , All Functor1 l
  , LamF ∈ l
  ) => Rec l a -> Rec l a
eta = everywhere
  $ MatchRec ? \case
    LAM x (App t (Var y))
       | x == y
       , not (Set.member x (freeVars t))
       , Just f <- gcast t
      -> f
  $ PassRec
-}

-- constProp ::
--   ( '[NumF,TruthF] ⊆ l
--   , All Functor1 l
--   ) => Rec l a -> Rec l a
-- constProp = everywhere
--   $ MatchRec ? \case
--     ADD (Int x) (Int y) -> Int $ x + y
--     e                   -> injRec e
--   $ MatchRec ? \case
--     IF  (Bool b) c a      -> if b then c else a
--     AND (Bool p) (Bool q) -> Bool $ p && q
--     OR  (Bool p) (Bool q) -> Bool $ p || q
--     NOT (Bool p)          -> Bool $ not p
--     e -> injRec e
--   $ PassRec

-- type is inferred with NoMonomorphismRestriction
-- e1 :: ('[LamF,DubF] ⊆ l_1) => Rec l_1 (a -> Int)
e1 :: Exp1 (Int -> Int)
e1 = Lam "x" (Dub (Var "x"))

e1' :: Exp2 (Int -> Int)
e1' = desugarDub e1

e2 :: Exp1 Int
e2 = Let "x" (Int 3) (Dub (Var "x"))

data VarsF :: (* -> *) -> * -> * where
  VARS :: Set String -> VarsF r a

pattern Vars s <- (prjRec -> Just (VARS s))
  where
  Vars s = injRec $ VARS s

getVars :: Rec '[VarsF] a -> Set String
getVars (Vars s) = s

data ShowF :: (* -> *) -> * -> * where
  SHOW :: String -> ShowF r a

pattern Sh x <- (prjRec -> Just (SHOW x))
  where
  Sh x = injRec $ SHOW x

getShow :: Rec '[ShowF] a -> String
getShow (Sh s) = s

data LamF r a where
  VAR :: Typeable a
      => String -> LamF r a
  LAM :: Typeable a
      => String -> r b -> LamF r (a -> b)
  APP :: r (a -> b) -> r a -> LamF r b

instance Forced LamF where
  forced = \case
    VAR x -> x `seq` (Constant ())
    LAM x b -> x `seq` (getConstant b) `seq` (Constant ())
    APP x y -> (getConstant x) `seq` (getConstant y) `seq` (Constant())

instance Render LamF where
  render = \case
    VAR x    -> Constant $ showString x
    LAM x b -> Constant $ showParen True
      $ showChar '\\'
      . showString x
      . showString " -> "
      . getConstant b
    APP a b -> Constant $ showParen True
      $ getConstant a
      . showChar ' '
      . getConstant b

instance Functor1 LamF where
  map1 f = \case
    VAR x   -> VAR x
    LAM x b -> LAM x (f b)
    APP a b -> APP (f a) (f b)

data LetF r a where
  LET :: Typeable a => String -> r a -> r b -> LetF r b

instance Forced LetF where
  forced (LET x a b) = x `seq` (getConstant a) `seq` (getConstant b) `seq` (Constant ())

instance Render LetF where
  render (LET x a b) = Constant $ showParen True
    $ showString "let "
    . showString x
    . showString " = "
    . getConstant a
    . showString " in "
    . getConstant b

instance Functor1 LetF where
  map1 f (LET x a b) = LET x (f a) (f b)

data TruthF r a where
  IF   :: r Bool -> r a -> r a -> TruthF r a
  BOOL :: Bool -> TruthF r Bool
  NOT  :: r Bool -> TruthF r Bool
  OR   :: r Bool -> r Bool -> TruthF r Bool
  AND  :: r Bool -> r Bool -> TruthF r Bool

instance Forced TruthF where
  forced = \case
    IF a b c -> (getConstant a) `seq` (getConstant b) `seq` (getConstant c) `seq` (Constant ())
    BOOL b -> b `seq` (Constant ())
    NOT a -> (getConstant a) `seq` (Constant ())
    OR a b -> (getConstant a) `seq` (getConstant b) `seq` (Constant ())
    AND a b -> (getConstant a) `seq` (getConstant b) `seq` (Constant ())

instance Render TruthF where
  render = \case
    IF t c a -> Constant $ showParen True
      $ showString "if "
      . getConstant t
      . showString " then "
      . getConstant c
      . showString " else "
      . getConstant a
    BOOL b -> Constant $ shows b

instance Functor1 TruthF where
  map1 f = \case
    IF t c a -> IF (f t) (f c) (f a)
    BOOL b   -> BOOL b

data NumF r a where
  INT    :: Int -> NumF r Int
  ADD    :: r Int -> r Int -> NumF r Int
  ISZERO :: r Int -> NumF r Bool

instance Forced NumF where
  forced = \case
    INT i -> i `seq` (Constant ())
    ADD a b -> (getConstant a) `seq` (getConstant b) `seq` (Constant ())
    ISZERO a -> (getConstant a) `seq` (Constant ())

instance Functor1 NumF where
  map1 f = \case
    INT i    -> INT i
    ADD x y  -> ADD (f x) (f y)
    ISZERO x -> ISZERO (f x)

instance Render NumF where
  render = \case
    INT i    -> Constant $ shows i
    ADD x y  -> Constant $ showParen True
      $ getConstant x
      . showString " + "
      . getConstant y
    ISZERO x -> Constant $ showParen True
      $ showString "isZero "
      . getConstant x


data DubF r a where
  DUB :: r Int -> DubF r Int

instance Functor1 DubF where
  map1 f (DUB x) = DUB (f x)

instance Render DubF where
  render (DUB x) = Constant $ showParen True
    $ showString "dub "
    . getConstant x

type L1 = '[DubF,LamF,LetF,TruthF,NumF]
type L2 = '[LamF,LetF,TruthF,NumF]
type L3 = '[LamF,TruthF,NumF]

type Exp1 = Rec L1
type Exp2 = Rec L2
type Exp3 = Rec L3

-- pattern Dub :: (a ~ Int) => (DubF ∈ fs) => Rec fs Int -> Rec fs a
pattern Dub a <- (prjRec -> Just (DUB a))
  where
  Dub a = injRec $ DUB a

-- pattern Add :: (a ~ Int) => (NumF ∈ fs) => Rec fs Int -> Rec fs Int -> Rec fs a
pattern Add x y <- (prjRec -> Just (ADD x y))
  where
  Add x y = injRec $ ADD x y

-- pattern Int :: (a ~ Int) => (NumF ∈ fs) => Int -> Rec fs a
pattern Int i <- (prjRec -> Just (INT i))
  where
  Int i = injRec $ INT i

-- pattern IsZero :: (a ~ Bool) => (NumF ∈ fs) => Rec fs Int -> Rec fs a
pattern IsZero x <- (prjRec -> Just (ISZERO x))
  where
  IsZero x = injRec $ ISZERO x

-- pattern If :: () => (TruthF ∈ fs) => Rec fs Bool -> Rec fs a -> Rec fs a -> Rec fs a
pattern If t c a <- (prjRec -> Just (IF t c a))
  where
  If t c a = injRec $ IF t c a

pattern Bool b <- (prjRec -> Just (BOOL b))
  where
  Bool b = injRec $ BOOL b

pattern Or x y <- (prjRec -> Just (OR x y))
  where
  Or x y = injRec $ OR x y

pattern And x y <- (prjRec -> Just (AND x y))
  where
  And x y = injRec $ AND x y

pattern Not x <- (prjRec -> Just (NOT x))
  where
  Not x = injRec $ NOT x

pattern Lam x b <- (prjRec -> Just (LAM x b))
  where
  Lam x b = injRec $ LAM x b

pattern App a b <- (prjRec -> Just (APP a b))
  where
  App a b = injRec $ APP a b

pattern Var x <- (prjRec -> Just (VAR x))
  where
  Var x = injRec $ VAR x

pattern Let x a b <- (prjRec -> Just (LET x a b))
  where
  Let x a b = injRec $ LET x a b

(?) :: ((forall x. f x -> g x) -> b) -> (forall x. f x -> g x) -> b
f ? g = f g
infixr 1 ?

(??) :: (a -> b) -> a -> b
(??) = ($)
infixr 1 ??

