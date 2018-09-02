{-# LANGUAGE TypeFamilies,
             GADTs,
             FlexibleContexts,
             ConstraintKinds,
             ScopedTypeVariables,
             TypeOperators,
             TupleSections #-}

module Yggdrasil.ExecutionModel (
    Operation, WeakRef, Action,
    Functionality(..), type (->>), external, weaken, abort, strengthenSelf, self, doSample,
    send, create, run
) where

import Control.Monad
import Data.Dynamic
import Yggdrasil.Distribution

newtype World = World [Dynamic]

-- | An operation is a stateful function of '(WeakRef, a) -> Action b' over the
-- state 's'.
type Operation s a b = (s, WeakRef, a) -> Action (s, b)

data Functionality s b = Functionality s (Action b)

data a ->> b where
    Ref :: Typeable s => Int -> Operation s a b -> (a ->> b)

-- | A weakened reference, that allows comparing entities for equality, but
-- nothing else.
newtype WeakRef = WeakRef Int deriving Eq

-- | A special reference indicating that something is external of the world.
-- This does not have a corresponding strong reference.
external :: WeakRef
external = WeakRef (-1)

-- | Weakens a functionality reference.
weaken :: (a ->> b) -> WeakRef
weaken (Ref idx _) = WeakRef idx

strengthen :: Typeable s =>
    World -> WeakRef -> Operation s a b -> Maybe (a ->> b)
strengthen (World []) _ _ = Nothing
strengthen (World (x:_)) (WeakRef 0) (f :: Operation s a b) = do
    _ :: s <- fromDynamic x
    return $ Ref 0 f
strengthen (World (_:xs)) wref f = do
    (Ref i f') <- strengthen (World xs) wref f
    return $ Ref (i+1) f'

new :: Typeable s => World -> s -> (World, WeakRef)
new (World xs) s = (World (xs ++ [toDyn s]), WeakRef (length xs))

safeIdx :: [a] -> Int -> Maybe a
safeIdx [] _ = Nothing
safeIdx (x:_) 0 = Just x
safeIdx _ i | i < 0 = Nothing
safeIdx (_:xs) i = safeIdx xs (i-1)

safeWriteIdx :: [a] -> Int -> a -> Maybe [a]
safeWriteIdx [] _ _ = Nothing
safeWriteIdx (_:xs) 0 x' = Just (x':xs)
safeWriteIdx _ i _ | i < 0 = Nothing
safeWriteIdx (x:xs) i x' = (:) x <$> safeWriteIdx xs (i-1) x'

data Action b where
    Abort :: Action b
    StrengthenSelf :: Typeable s => Operation s a b -> Action (a ->> b)
    Self :: Action WeakRef
    Sample :: Distribution b -> Action b
    Send :: (a ->> b) -> a -> Action b
    Create :: Typeable s => Functionality s b -> Action b
    Compose :: Action c -> (c -> Action b) -> Action b

-- Export visible constructors as functions.
-- | Aborts the current execution.
abort :: Action b
abort = Abort
-- | Attempts to add a new operation on ourselves.
-- This action will fail (effectively aborting) if our state is not of type
-- 's'.
strengthenSelf :: Typeable s => Operation s a b -> Action (a ->> b)
strengthenSelf = StrengthenSelf
-- | Obtain a weak reference on ourselves.
self :: Action WeakRef
self = Self
-- | Sample from a distribution
doSample :: Distribution b -> Action b
doSample = Sample
-- | Send a message to a receipient we know the reference of.
-- Unless the receipient aborts, he must eventually respond.
send :: a ->> b -> a -> Action b
send = Send
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
run :: Sampler s => s -> Action b -> Maybe (b, s)
run s a = (\(_, b, s') -> (b, s')) <$> run' s (World []) external a

run' :: Sampler s =>
    s -> World -> WeakRef -> Action b -> Maybe (World, b, s)
run' _ _ _ Abort = Nothing
run' s wld slf (StrengthenSelf f) =
    (wld, , s) <$> strengthen wld slf f
run' s wld slf Self = return (wld, slf, s)
run' s wld _ (Sample d) = let (y, s') = sample s d in Just (wld, y, s')
run' s (World xs) from (Send to@(Ref idx func) m) = do
    dyns <- safeIdx xs idx
    st <- fromDynamic dyns
    let action = func (st, from, m)
    (World xs', (st', y), s') <- run' s (World xs) (weaken to) action
    xs'' <- safeWriteIdx xs' idx (toDyn st')
    return (World xs'', y, s')
    -- Note: This could cause a re-entrancy style bug!
run' s wld _ (Create (Functionality st a)) =
    let (wld', from') = new wld st in run' s wld' from' a
run' s wld from (Compose a f) = do
    (wld', b, s') <- run' s wld from a
    run' s' wld' from (f b)
