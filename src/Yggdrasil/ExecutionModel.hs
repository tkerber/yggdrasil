{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}

module Yggdrasil.ExecutionModel
  ( Operation
  , Ref(External)
  , Action
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

-- | An operation is a stateful function of @('Ref, a) -> 'Action' b@ over
-- the state @s@.
type Operation s c a b = c -> Ref s -> a -> Action s (c, b)

data Functionality s c b =
  Functionality c
                (Action s b)

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

data Action s b
  = Abort
  | Sample (Distribution b)
  | forall a. Send (SendRef s a b)
                   a
  | forall c. Create (Functionality s c b)
  | forall c. Compose (Action s c)
                      (c -> Action s b)

-- | Attempts to add a new operation on ourselves.
-- This action will fail (effectively aborting) if our state is not of type
-- 's'.
--interface :: Operation s c a b -> Action (a -> Action b)
--interface = StrengthenSelf
--
--interface' :: Typeable s => Operation s () b -> Action (Action b)
--interface' op = (\f -> f ()) <$> interface op
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
run' _ (Create (Functionality c a)) = do
  ptr <- lift . lift $ newSTRef c
  id' <- lift . lift $ newSTRef ()
  run' (Ref ptr id') a
run' from (Compose a f) = run' from a >>= run' from . f
