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

pass1 :: DesugarDub f g => Fix f -> Fix g
pass1 (In t) = pass t

class DesugarDub f g where
    pass :: DesugarDub h g => f (Fix h) -> Fix g

instance (DesugarDub a g, DesugarDub b g) => DesugarDub (a :+: b) g where
    pass (L a) = pass a
    pass (R b) = pass b


