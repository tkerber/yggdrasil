{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module Yggdrasil.HList
  ( HList(..)
  ) where

data HList :: [*] -> * where
  Nil :: HList '[]
  Cons :: a -> HList as -> HList (a ': as)
