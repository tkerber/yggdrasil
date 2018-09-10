{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Yggdrasil.HList
  ( HList(..)
  , type (+|+)
  , HAppend((+++))
  , HSplit(hsplit)
  ) where

data HList :: [*] -> * where
  Nil :: HList '[]
  (:::) :: a -> HList as -> HList (a ': as)

type family (as :: [k]) +|+ (bs :: [k]) :: [k] where
  '[] +|+ bs = bs
  (a ': as) +|+ bs = a ': (as +|+ bs)

class HAppend as bs where
  (+++) :: HList as -> HList bs -> HList (as +|+ bs)

instance HAppend '[] bs where
  _ +++ bs = bs

instance HAppend as bs => HAppend (a ': as) bs where
  (a ::: as) +++ bs = a ::: (as +++ bs)

class HSplit hs as bs where
  hsplit :: HList hs -> (HList as, HList bs)

instance HSplit bs '[] bs where
  hsplit bs = (Nil, bs)

instance HSplit hs as bs => HSplit (a ': hs) (a ': as) bs where
  hsplit (h ::: hs) = let (as, bs) = hsplit @hs @as @bs hs in (h ::: as, bs)
