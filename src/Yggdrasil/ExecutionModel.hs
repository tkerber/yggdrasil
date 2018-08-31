{-# LANGUAGE TypeFamilies, GADTs, FlexibleContexts, ConstraintKinds, ScopedTypeVariables #-}

module Yggdrasil.ExecutionModel (
    Funct, TypFunct, Ref, WeakRef, Action, external, weaken, abort,
    strengthenSelf, self, doSample, send, create, run
) where

import Control.Monad
import Data.Dynamic
import System.Random
import Yggdrasil.Distribution

newtype World = World [Dynamic]

-- | A functionality is a stateful function of '(WeakRef, a) -> Action b' over
-- the state 's'.
type Funct s a b = (s, WeakRef, a) -> (s, Action b)

-- | A typeable functionality
type TypFunct s a b = (Typeable s, Typeable a, Typeable b)

-- | References a functionality, which has some state in the world. A 'Ref' is
-- only valid for the world it was created in, and has undefined behaviour when
-- used elsewhere.
data Ref s a b = Ref
    { index :: Int
    , func :: Funct s a b }

-- | A weakened reference, that allows comparing entities for equality, but
-- nothing else.
newtype WeakRef = WeakRef Int deriving Eq

-- | A special reference indicating that something is external of the world.
-- This does not have a corresponding strong reference.
external :: WeakRef
external = WeakRef (-1)

-- | Weakens a functionality reference.
weaken :: Ref s a b -> WeakRef
weaken = WeakRef . index

strengthen :: TypFunct s a b =>
    World -> WeakRef -> Funct s a b -> Maybe (Ref s a b)
strengthen (World []) _ _ = Nothing
strengthen (World (x:_)) (WeakRef 0) (f :: Funct s a b) = do
    _ :: s <- fromDynamic x
    return $ Ref 0 f
strengthen (World (_:xs)) wref f = do
    (Ref i f') <- strengthen (World xs) wref f
    return $ Ref (i+1) f'

new :: TypFunct s a b =>
    World -> s -> Funct s a b -> (World, Ref s a b)
new (World xs) s f = (World (xs ++ [toDyn s]), Ref (length xs) f)

safeIdx :: [a] -> Int -> Maybe a
safeIdx [] _ = Nothing
safeIdx (x:_) 0 = Just x
safeIdx _ i | i < 0 = Nothing
safeIdx (_:xs) i = safeIdx xs (i-1)

safeWriteIdx :: [a] -> Int -> a -> Maybe [a]
safeWriteIdx [] _ _ = Nothing
safeWriteIdx (_:xs) 0 x' = Just (x':xs)
safeWriteIdx _ i _ | i < 0 = Nothing
safeWriteIdx (x:xs) i x' = fmap ((:) x) $ safeWriteIdx xs (i-1) x'

update :: TypFunct s a b =>
    World -> WeakRef -> Ref s a b -> a -> Maybe (World, Action b)
update (World xs) from to msg = do
    dyns <- safeIdx xs (index to)
    s <- fromDynamic dyns
    let (s', a) = (func to) (s, from, msg)
    xs' <- safeWriteIdx xs (index to) (toDyn s')
    return $ (World xs', a)

data Action b where
    Abort :: Action b
    StrengthenSelf :: TypFunct s a b => Funct s a b -> Action (Ref s a b)
    Self :: Action WeakRef
    Sample :: Distribution b -> Action b
    Send :: TypFunct s a b => Ref s a b -> a -> Action b
    Create :: TypFunct s a b => s -> Funct s a b -> Action (Ref s a b)
    Compose :: Action c -> (c -> Action b) -> Action b

-- Export visible constructors as functions.
-- | Aborts the current execution.
abort :: Action b
abort = Abort
-- | Attempts to add a new operation on ourselves.
-- This action will fail (effectively aborting) if our state is not of type
-- 's'.
strengthenSelf :: TypFunct s a b => Funct s a b -> Action (Ref s a b)
strengthenSelf = StrengthenSelf
-- | Obtain a weak reference on ourselves.
self :: Action WeakRef
self = Self
-- | Sample from a distribution
doSample :: Distribution b -> Action b
doSample = Sample
-- | Send a message to a receipient we know the reference of.
-- Unless the receipient aborts, he must eventually respond.
send :: TypFunct s a b => Ref s a b -> a -> Action b
send = Send
-- | Creates a new autonomous party, with a given initial state, and a given
-- program.
create :: TypFunct s a b => s -> Funct s a b -> Action (Ref s a b)
create = Create

instance Functor Action where
    fmap f x = pure f <*> x
instance Applicative Action where
    pure = Sample . pure
    (<*>) = ap
instance Monad Action where
    a >>= b = Compose a b

-- | Execute a top-level action in the Yggdrasil execution model.
run :: RandomGen g => g -> Action b -> (Maybe b, g)
run g a = let (r, g') = run' g (World []) external a in (fmap snd r, g')

run' :: RandomGen g =>
    g -> World -> WeakRef -> Action b -> (Maybe (World, b), g)
run' g _ _ Abort = (Nothing, g)
run' g wld slf (StrengthenSelf f) =
    (fmap (\r -> (wld, r)) (strengthen wld slf f), g)
run' g wld slf Self = (Just (wld, slf), g)
run' g wld _ (Sample d) = let (y, g') = sample g d in (Just (wld, y), g')
run' g wld from (Send ref m) = case update wld from ref m of
    Just (wld', a) -> run' g wld' (weaken ref) a
    Nothing -> (Nothing, g)
run' g wld _ (Create s f) = (Just (new wld s f), g)
run' g wld from (Compose a f) = case run' g wld from a of
    (Just (wld', b), g') -> run' g' wld' from (f b)
    (Nothing, g') -> (Nothing, g')
