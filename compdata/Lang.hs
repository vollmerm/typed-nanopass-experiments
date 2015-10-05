{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Lang where

import           Data.Comp
import           Data.Comp.Derive
import           Data.Comp.Desugar
import           Data.Comp.Equality
import           Data.Comp.Show

data LDouble e = LDouble e
data Plus    e = Plus e e
data Times   e = Times e e
data LConst  e = LConst Int
data Lamb    e = Lamb e
data Apply   e = Apply e e
data Var     e = Var Int
data Let     e = Let e e

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

-- Lift the evaluation algebra to a catamorphism
eval :: (Functor f, Eval f v) => Term f -> Term v
eval = cata evalAlg

instance (f :<: v) => Eval f v where  evalAlg = inject -- default instance

type L1 = LDouble :+: Plus :+: Times :+: LConst
type L2 = Plus :+: Times :+: LConst

$(derive [makeFunctor, makeTraversable, makeFoldable,
          makeEqF, makeShowF, makeOrdF, smartConstructors, smartAConstructors]
           [''LDouble, ''Plus, ''Times, ''LConst, ''Lamb, ''Apply, ''Var, ''Let])

instance (Plus :<: f, Functor f) => Desugar LDouble f where
  desugHom' (LDouble e) = e `iPlus` e

c1 :: Term L1
c1 = iLDouble $ iLConst 2

c1' :: Term L2
c1' = desugar c1

instance (Lamb :<: f, Apply :<: f, Functor f) => Desugar Let f where
  desugHom' (Let e1 e2) = (iLamb e2) `iApply` e1

type L3 = Lamb :+: Let :+: LConst :+: Apply :+: Var :+: Plus
type L4 = Lamb :+: LConst :+: Apply :+: Var :+: Plus

c2 :: Term L3
c2 = iLet (iLConst 1) ((iVar 0) `iPlus` (iLConst 2))

c2' :: Term L4
c2' = desugar c2
