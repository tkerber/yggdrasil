{-# LANGUAGE GADTs               #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Yggdrasil.ExecutionModel
  ( Operation
  , Ref
  , Action
  , Functionality(..)
  , external
  , weaken
  , abort
  , interface
  , interface'
  , self
  , doSample
  , create
  , run
  ) where

import           Control.Monad             (ap)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (MaybeT), runMaybeT)
import           Data.Dynamic              (Dynamic, Typeable, fromDynamic,
                                            toDyn)
import           Yggdrasil.Distribution    (Distribution)

newtype World =
  World [Dynamic]

-- | An operation is a stateful function of @('Ref, a) -> 'Action' b@ over
-- the state @s@.
type Operation s a b = (s, Ref, a) -> Action (s, b)

data Functionality s b =
  Functionality s
                (Action b)

data SendRef a b where
  SendRef :: Typeable s => Int -> Operation s a b -> SendRef a b

-- | A weakened reference, that allows comparing entities for equality, but
-- nothing else.
newtype Ref =
  Ref Int
  deriving (Eq)

-- | A special reference indicating that something is external of the world.
-- This does not have a corresponding strong reference.
external :: Ref
external = Ref (-1)

weaken :: SendRef a b -> Ref
weaken (SendRef idx _) = Ref idx

strengthen ::
     Typeable s => World -> Ref -> Operation s a b -> Maybe (SendRef a b)
strengthen (World []) _ _ = Nothing
strengthen (World (x:_)) (Ref 0) (f :: Operation s a b) = do
  _ :: s <- fromDynamic x
  return $ SendRef 0 f
strengthen (World (_:xs)) wref f = do
  (SendRef i f') <- strengthen (World xs) wref f
  return $ SendRef (i + 1) f'

new :: Typeable s => World -> s -> (World, Ref)
new (World xs) s = (World (xs ++ [toDyn s]), Ref (length xs))

safeIdx :: [a] -> Int -> Maybe a
safeIdx [] _ = Nothing
safeIdx (x:_) 0 = Just x
safeIdx _ i
  | i < 0 = Nothing
safeIdx (_:xs) i = safeIdx xs (i - 1)

safeWriteIdx :: [a] -> Int -> a -> Maybe [a]
safeWriteIdx [] _ _ = Nothing
safeWriteIdx (_:xs) 0 x' = Just (x' : xs)
safeWriteIdx _ i _
  | i < 0 = Nothing
safeWriteIdx (x:xs) i x' = (:) x <$> safeWriteIdx xs (i - 1) x'

data Action b where
  Abort :: Action b
  StrengthenSelf :: Typeable s => Operation s a b -> Action (a -> Action b)
  Self :: Action Ref
  Sample :: Distribution b -> Action b
  Send :: SendRef a b -> a -> Action b
  Create :: Typeable s => Functionality s b -> Action b
  Compose :: Action c -> (c -> Action b) -> Action b

-- Export visible constructors as functions.
-- | Aborts the current execution.
abort :: Action b
abort = Abort

-- | Attempts to add a new operation on ourselves.
-- This action will fail (effectively aborting) if our state is not of type
-- 's'.
interface :: Typeable s => Operation s a b -> Action (a -> Action b)
interface = StrengthenSelf

interface' :: Typeable s => Operation s () b -> Action (Action b)
interface' op = (\f -> f ()) <$> interface op

-- | Obtain a weak reference on ourselves.
self :: Action Ref
self = Self

-- | Sample from a distribution
doSample :: Distribution b -> Action b
doSample = Sample

-- | Creates a new autonomous party, with a given initial state, and a given
-- program.
create :: Typeable s => Functionality s b -> Action b
create = Create

instance Functor Action where
  fmap f x = pure f <*> x

instance Applicative Action where
  pure = Sample . pure
  (<*>) = ap

instance Monad Action where
  a >>= b = Compose a b

-- | Execute a top-level action in the Yggdrasil execution model.
run :: Action b -> Distribution (Maybe b)
run a = runMaybeT $ snd <$> run' (World []) external a

run' :: World -> Ref -> Action b -> MaybeT Distribution (World, b)
run' _ _ Abort = MaybeT $ return Nothing
run' wld slf (StrengthenSelf f) =
  MaybeT $ return $ (wld, ) . Send <$> strengthen wld slf f
run' wld slf Self = MaybeT $ return $ Just (wld, slf)
run' wld _ (Sample d) = lift $ (wld, ) <$> d
run' (World xs) from (Send to@(SendRef idx func) m) = do
  dyns <- MaybeT $ return $ safeIdx xs idx
  st <- MaybeT $ return $ fromDynamic dyns
  let action = func (st, from, m)
  (World xs', (st', y)) <- run' (World xs) (weaken to) action
  xs'' <- MaybeT $ return $ safeWriteIdx xs' idx (toDyn st')
  return (World xs'', y)
    -- Note: This could cause a re-entrancy style bug!
run' wld _ (Create (Functionality st a)) =
  let (wld', from') = new wld st
   in run' wld' from' a
run' wld from (Compose a f) = do
  (wld', b) <- run' wld from a
  run' wld' from (f b)
