{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Util where

import           Language.Haskell.TH

removeForm :: Name -> Name -> Q [Dec]
removeForm = undefined

getFields :: Name -> Q [Con]
getFields name = do
  TyConI (DataD _ _ _ fields _) <- reify name
  return fields

