{-# LANGUAGE GADTs               #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Yggdrasil.ExecutionModel
  ( Operation
  , Ref(External)
  , Action
  , Functionality(..)
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
import           Yggdrasil.Distribution    (Distribution, coin)

data World =
  World [Dynamic]
        [Bool]

-- | An operation is a stateful function of @('Ref, a) -> 'Action' b@ over
-- the state @s@.
type Operation s a b = (s, Ref, a) -> Action (s, b)

data Functionality s b =
  Functionality s
                (Action b)

data SendRef a b where
  SendRef :: Typeable s => RealRef -> Operation s a b -> SendRef a b

data RealRef =
  RealRef Int
          [Bool]
  deriving (Eq)

data Ref
  = Ref RealRef
  | External
  deriving (Eq)

weaken :: SendRef a b -> Ref
weaken (SendRef ref _) = Ref ref

strengthen ::
     Typeable s => World -> RealRef -> Operation s a b -> Maybe (SendRef a b)
strengthen (World [] _) _ _ = Nothing
strengthen (World _ wid) (RealRef _ wid') _
  | wid /= wid' = Nothing
strengthen (World (x:_) _) ref@(RealRef 0 _) (f :: Operation s a b) = do
  _ :: s <- fromDynamic x
  return $ SendRef ref f
strengthen (World (_:xs) wid) wref f = do
  (SendRef (RealRef i w) f') <- strengthen (World xs wid) wref f
  return $ SendRef (RealRef (i + 1) w) f'

new :: Typeable s => World -> s -> (World, Ref)
new (World xs wid) s =
  (World (xs ++ [toDyn s]) wid, Ref (RealRef (length xs) wid))

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
run :: Int -> Action b -> Distribution (Maybe b)
run secparam a =
  runMaybeT
    (do wid <- (lift . sequence) $ map (const coin) [0 .. secparam]
        snd <$> run' (World [] wid) External a)

run' :: World -> Ref -> Action b -> MaybeT Distribution (World, b)
run' _ _ Abort = MaybeT $ return Nothing
run' _ External (StrengthenSelf _) = MaybeT $ return Nothing
run' wld (Ref slf) (StrengthenSelf f) =
  MaybeT $ return $ (wld, ) . Send <$> strengthen wld slf f
run' wld slf Self = MaybeT $ return $ Just (wld, slf)
run' wld _ (Sample d) = lift $ (wld, ) <$> d
run' (World _ wid) _ (Send (SendRef (RealRef _ wid') _) _)
  | wid /= wid' = MaybeT $ return Nothing
run' wld@(World xs _) from (Send (SendRef to@(RealRef idx _) func) m) = do
  dyns <- MaybeT $ return $ safeIdx xs idx
  st <- MaybeT $ return $ fromDynamic dyns
  let action = func (st, from, m)
  (World xs' wid', (st', y)) <- run' wld (Ref to) action
  xs'' <- MaybeT $ return $ safeWriteIdx xs' idx (toDyn st')
  return (World xs'' wid', y)
    -- Note: This could cause a re-entrancy style bug!
run' wld _ (Create (Functionality st a)) =
  let (wld', from') = new wld st
   in run' wld' from' a
run' wld from (Compose a f) = do
  (wld', b) <- run' wld from a
  run' wld' from (f b)
