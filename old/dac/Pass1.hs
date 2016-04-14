{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Pass1 where

import           LangDef


-------------------------------------------------------------------
-- This is the interesting case.

instance DesugarDub Dub where
    pass (Dub (In e)) = let e' = pass e in add e' e'

--
-------------------------------------------------------------------




pass1 :: (DesugarDub h,
          Val :<: h, Add :<: h, Mul :<: h, Dub :<: h,
          Val :<: g, Add :<: g, Mul :<: g)
      => Fix h -> Fix g
pass1 (In t) = pass t

class DesugarDub f where
    pass :: (DesugarDub h,
             Val :<: h, Add :<: h, Mul :<: h, Dub :<: h,
             Val :<: g, Add :<: g, Mul :<: g)
         => f (Fix h) -> Fix g

instance (DesugarDub a, DesugarDub b) => DesugarDub (a :+: b) where
    pass (L a) = pass a
    pass (R b) = pass b

instance DesugarDub Add where
    pass (Add (In e1) (In e2)) = add (pass e1) (pass e2)

instance DesugarDub Mul where
    pass (Mul (In e1) (In e2)) = mul (pass e1) (pass e2)

instance DesugarDub Val where
    pass (Val e) = val e

v1 = add (val 1) (val 2) :: Fix (Add :+: Val)
v2 = dub v1 :: Fix (Dub :+: Add :+: Val)
-- v2' = pass1 v2
