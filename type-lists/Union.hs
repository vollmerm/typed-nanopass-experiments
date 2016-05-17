{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Union where

import Control.Monad
import GHC.Exts (Constraint)

data Union :: [*] -> * where
  InL :: a -> Union (a ': as)
  InR :: Union as -> Union (a ': as)

type AllEq     as = AllC Eq as
type AllOrd    as = (AllEq as, AllC Ord as)
type AllShow   as = AllC Show as

deriving instance AllEq   as => Eq   (Union as)
deriving instance AllOrd  as => Ord  (Union as)
deriving instance AllShow as => Show (Union as)

unionØ :: Union '[] -> a
unionØ _ = error "impossible empty union"

type family AllC (f :: k -> Constraint) (as :: [k]) :: Constraint where
  AllC f '[]       = (() :: Constraint)
  AllC f (a ': as) = (f a, AllC f as)

class a ∈ (as :: [*]) where
  inj1 :: a -> Union as
  prj1 :: MonadPlus m => Union as -> m a
infix 4 ∈

instance {-# OVERLAPPING #-} a ∈ (a ': as) where
  inj1 = InL
  prj1 = \case
    InL a -> return a
    _     -> mzero

instance {-# OVERLAPPABLE #-} (a ∈ as) => a ∈ (b ': as) where
  inj1 = InR . inj1
  prj1 = \case 
   InR u -> prj1 u
   _     -> mzero

class Subset as bs => (as :: [*]) ⊆ (bs :: [*]) where
  type Subset as bs :: Constraint
  inj :: Union as -> Union bs
  prj :: MonadPlus m => Union bs -> m (Union as)
infix 4 ⊆

instance '[] ⊆ bs where
  type Subset '[] bs = (() :: Constraint)
  inj   = unionØ
  prj _ = mzero

instance (a ∈ bs, as ⊆ bs) => (a ': as) ⊆ bs where
  type Subset (a ': as) bs = (a ∈ bs, as ⊆ bs)
  inj = \case
    InL a -> inj1 a
    InR u -> inj u
  prj u = case prj1 u of
    Just a -> return $ InL a
    _      -> InR <$> prj u

