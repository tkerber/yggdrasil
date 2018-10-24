{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}

-- | Defines the basic model of execution for Yggdrasil. This is modelled
-- after, but not directly equal to, the
-- <https://eprint.iacr.org/2000/068 Universal Composability framework by Ran Canetti>.
--
-- Usage typically involves constructing a complex 'Action', and then 'run'ning
-- it.
module Yggdrasil.ExecutionModel
  ( Operation
  , Action(Abort, Sample, Create, SecParam)
  , Operations
  , Interfaces
  , Functionality(..)
  , InterfaceMap(..)
  , ForceSample(forceSample)
  , run
  ) where

import           Control.Monad             (ap)
import           Control.Monad.Fail        (MonadFail (fail))
import           Control.Monad.ST          (ST, runST)
import           Control.Monad.State.Lazy  (StateT, runStateT)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (MaybeT), runMaybeT)
import           Data.STRef                (STRef, newSTRef, readSTRef,
                                            writeSTRef)
import           Yggdrasil.Distribution    (Distribution, DistributionT (DistributionT, runDistT),
                                            coin, liftDistribution)
import           Yggdrasil.HList           (HList ((:::), Nil))

-- | Describes what a node with internal state of type @c@ does when passed an
-- input of type @a@ by @Ref s@.
type Operation s c a b = a -> StateT c (Action s) b

-- | Given a list of tuples of input and output types, construct a
-- corresponding list of 'Operation' types.
type family Operations s c (xs :: [(*, *)]) = (ys :: [*]) | ys -> xs where
  Operations s c '[] = '[]
  Operations s c ('( a, b) ': xs) = Operation s c a b ': Operations s c xs

-- | Given a list of tuples of input and output types, construct a
-- corresponding list of 'Interface' types.
type family Interfaces s (xs :: [(*, *)]) = (ys :: [*]) | ys -> xs where
  Interfaces s '[] = '[]
  Interfaces s ('( a, b) ': xs) = (a -> Action s b) ': Interfaces s xs

-- | A functionality is a stateful node, with an initial state, and an
-- interface typed by a list of input/output type tuples, and defined through a
-- 'HList' of 'Operation's.
data Functionality s c ops =
  Functionality c
                (HList (Operations s c ops))

data SendRef s a b =
  forall c. SendRef (STRef s c)
                    (Operation s c a b)

-- | Yggdrasil's version of 'IO'. Is self-contained, and can be opened with
-- 'run'.
data Action s b where
  -- | Fail. This should be used over actual errors!
  Abort :: Action s b
  -- | Retrieves the security parameter of the running system.
  SecParam :: Action s Int
  -- | Samples from a distribution.
  Sample :: Distribution b -> Action s b
  Send :: SendRef s a b -> a -> Action s b
  -- | Creates a new node from a functionality specification.
  Create
    :: InterfaceMap s c ops
    => Functionality s c (ops :: [(*, *)])
    -> Action s (HList (Interfaces s ops))
  Compose :: Action s c -> (c -> Action s b) -> Action s b

instance Functor (Action s) where
  fmap f x = pure f <*> x

instance Applicative (Action s) where
  pure = Sample . pure
  (<*>) = ap

instance Monad (Action s) where
  a >>= b = Compose a b

instance MonadFail (Action s) where
  fail _ = Abort

-- | Simulates a world running an external action.
run :: (forall s. Action s b) -> DistributionT Maybe b
run a =
  DistributionT $ \rng -> runST $ runMaybeT $ runDistT (run' a) rng

run' :: Action s b -> DistributionT (MaybeT (ST s)) b
run' Abort = DistributionT $ \_ -> MaybeT $ return Nothing
-- TODO: Make a parameter
run' SecParam = return 128
run' (Sample d) = liftDistribution d
run' (Send (SendRef (ptr :: STRef s c) op) msg) = do
  c <- lift . lift $ readSTRef ptr
  (b, c') <- run' (runStateT (op msg) c)
  lift . lift $ writeSTRef ptr c'
  return b
run' (Create (Functionality c ops)) = do
  ptr <- lift . lift $ newSTRef c
  return $ ifmap ptr ops
run' (Compose a f) = run' a >>= run' . f

-- | States we can create interfaces from operations. Implemented for all @ts@.
class InterfaceMap s c (ts :: [(*, *)]) where
  ifmap :: STRef s c -> HList (Operations s c ts) -> HList (Interfaces s ts)

instance InterfaceMap s c '[] where
  ifmap _ Nil = Nil

instance InterfaceMap s c as => InterfaceMap s c ('( a, b) ': as) where
  ifmap ref (x ::: xs) = Send (SendRef ref x) ::: ifmap ref xs

-- | States that we can forcibly sample from a type, such that with negligible
-- probabily there is a collision between samples.
class ForceSample t where
  forceSample :: Action s t

instance ForceSample [Bool] where
  forceSample = SecParam >>= (\sp -> sequence [Sample coin | _ <- [0 .. sp]])
