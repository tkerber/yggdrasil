{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}

module Yggdrasil.ExecutionModel
  ( Operation
  , SendRef
  , Ref(External)
  , Action(..)
  , Operations
  , Interfaces
  , InterfaceMap
  , Functionality(..)
  , weaken
  , run
  ) where

import           Control.Monad             (ap)
import           Control.Monad.ST          (ST, runST)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (MaybeT), runMaybeT)
import           Data.STRef                (STRef, newSTRef, readSTRef,
                                            writeSTRef)
import           Yggdrasil.Distribution    (Distribution, DistributionT (DistributionT, runDistT),
                                            liftDistribution)
import           Yggdrasil.HList           (HList (Cons, Nil))

type Operation s c a b = c -> Ref s -> a -> Action s (c, b)

type family Operations s c (xs :: [*]) :: [*]

type instance Operations s c '[] = '[]

type instance Operations s c ((a, b) ': xs) =
     Operation s c a b ': Operations s c xs

type family Interfaces s (xs :: [*]) = (ys :: [*]) | ys -> xs

type instance Interfaces s '[] = '[]

type instance Interfaces s ((a, b) ': xs) =
     SendRef s a b ': Interfaces s xs

data Functionality s c ops =
  Functionality c
                (HList (Operations s c ops))

type ID s = STRef s ()

data SendRef s a b =
  forall c. SendRef (STRef s c)
                    (ID s)
                    (Operation s c a b)

data Ref s
  = forall a. Ref (STRef s a)
                  (ID s)
  | External

instance Eq (Ref s) where
  External == External = True
  Ref _ a == Ref _ b = a == b
  _ == _ = False

weaken :: SendRef s a b -> Ref s
weaken (SendRef ref id' _) = Ref ref id'

data Action s b where
  Abort :: Action s b
  Sample :: Distribution b -> Action s b
  Send :: SendRef s a b -> a -> Action s b
  Create
    :: InterfaceMap s c ops
    => Functionality s c ops
    -> Action s (HList (Interfaces s ops))
  Compose :: Action s c -> (c -> Action s b) -> Action s b

instance Functor (Action s) where
  fmap f x = pure f <*> x

instance Applicative (Action s) where
  pure = Sample . pure
  (<*>) = ap

instance Monad (Action s) where
  a >>= b = Compose a b

run :: (forall s. Action s b) -> DistributionT Maybe b
run a =
  DistributionT $ \rng -> runST $ runMaybeT $ runDistT (run' External a) rng

run' :: Ref s -> Action s b -> DistributionT (MaybeT (ST s)) b
run' _ Abort = DistributionT $ \_ -> MaybeT $ return Nothing
run' _ (Sample d) = liftDistribution d
run' from (Send to@(SendRef (ptr :: STRef s c) _ op) msg) = do
  c <- lift . lift $ readSTRef ptr
  (c', b) <- run' (weaken to) (op c from msg)
  lift . lift $ writeSTRef ptr c'
  return b
run' _ (Create (Functionality c ops)) = do
  ptr <- lift . lift $ newSTRef c
  id' <- lift . lift $ newSTRef ()
  return $ ifmap ptr id' ops
run' from (Compose a f) = run' from a >>= run' from . f

-- | Dictates we can create interfaces from operations.
class InterfaceMap s c (ts :: [*]) where
  ifmap ::
       STRef s c -> ID s -> HList (Operations s c ts) -> HList (Interfaces s ts)

instance InterfaceMap s c '[] where
  ifmap _ _ Nil = Nil

instance InterfaceMap s c as => InterfaceMap s c ((a, b) ': as) where
  ifmap ref id' (Cons x xs) = Cons (SendRef ref id' x) (ifmap ref id' xs)
