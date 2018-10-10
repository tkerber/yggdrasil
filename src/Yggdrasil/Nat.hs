{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Yggdrasil.Nat
  ( Nat
  , Zero
  , Succ
  , NCopies
  , Zn
  , ForEach(foreach)
  , IdApplied(idApplied)
  , mkZn
  , unZn
  ) where

import           Data.Maybe      (fromJust)
import           Yggdrasil.HList (Applied, HList ((:::), Nil))

data Zero

data Succ n

class Nat n where
  asInt :: Integral i => i

instance Nat Zero where
  asInt = 0

instance Nat n => Nat (Succ n) where
  asInt = asInt @n + 1

data Zn n =
  Zn Integer
  deriving (Eq, Show, Ord)

mkZn ::
     forall n. Nat n
  => Integer
  -> Maybe (Zn n)
mkZn x
  | x < 0 = Nothing
  | x > asInt @n = Nothing
  | otherwise = Just (Zn x)

unZn :: Zn n -> Integer
unZn (Zn n) = n

promote :: Zn n -> Zn (Succ n)
promote (Zn n) = Zn n

type family NCopies n (a :: k) = (as :: [k]) | as -> n
  --NCopies n (m a) = Applied m (NCopies n a)
 where
  NCopies Zero a = '[]
  NCopies (Succ n) a = a ': NCopies n a

class ForEach n a where
  foreach :: (Zn n -> a) -> HList (NCopies n a)

instance ForEach Zero a where
  foreach _ = Nil

instance (Nat n, ForEach n a) => ForEach (Succ n) a where
  foreach f =
    f (fromJust (mkZn ((asInt @n) - 1))) ::: foreach @n @a (f . promote)

class IdApplied m n as where
  idApplied :: HList (NCopies n (m as)) -> HList (Applied m (NCopies n as))

instance IdApplied m Zero as where
  idApplied _ = Nil

instance IdApplied m n as => IdApplied m (Succ n) as where
  idApplied (a ::: as) = a ::: idApplied @m @n @as as
