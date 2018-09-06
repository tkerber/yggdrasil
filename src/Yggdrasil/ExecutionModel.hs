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
import Control.Monad.ST (ST)
import Data.STRef (STRef)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (MaybeT), runMaybeT)
import           Data.Dynamic              (Dynamic, Typeable, fromDynamic,
                                            toDyn)
import           Yggdrasil.Distribution    (Distribution, coin)

-- | An operation is a stateful function of @('Ref, a) -> 'Action' b@ over
-- the state @s@.
type Operation s c a b = (c, Ref s, a) -> Action s (c, b)

data Functionality s b =
  Functionality s
                (Action s b)

data SendRef s a b = forall c. SendRef (STRef s c) (Operation s c a b)

data Ref s
  = forall a. Ref (STRef s a)
  | External

instance Eq (Ref s) where
  External == External = True
  Ref (r1::STRef s a) == Ref (r2::STRef s a) = r1 == r2

weaken :: SendRef s a b -> Ref s
weaken (SendRef ref _) = Ref ref

data Action s b = Abort | Sample (Distribution b) | forall a. Send (SendRef s a b) a | forall c. Create (Functionality c b) | forall c. Compose (Action s c) (c -> Action s b)

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

run' :: Ref s -> Action s b -> ST s (MaybeT Distribution b)
run' _ Abort = return MaybeT $ return Nothing
run' _ (Sample d) = return $ lift d
run' from (Send (SendRef to op) msg) = do
    c <- readSTRef to
    (c', b) <- run' (weaken to) (op (c, from, msg))
    writeSTRef to c'
    return b
run' from (Create (Functionality c act)) = do
    ref <- newSTRef c
    run' (Ref ref) act
run' from (Compose a f) = do
    c <- run' from a
    run' from (f c)

-- | Execute a top-level action in the Yggdrasil execution model.
--run :: Int -> Action b -> Distribution (Maybe b)
--run secparam a =
--  runMaybeT
--    (do wid <- (lift . sequence) $ map (const coin) [0 .. secparam]
--        snd <$> run' (World [] wid) External a)

--run' :: World -> Ref -> Action b -> MaybeT Distribution (World, b)
--run' _ _ Abort = MaybeT $ return Nothing
--run' _ External (StrengthenSelf _) = MaybeT $ return Nothing
--run' wld (Ref slf) (StrengthenSelf f) =
--  MaybeT $ return $ (wld, ) . Send <$> strengthen wld slf f
--run' wld slf Self = MaybeT $ return $ Just (wld, slf)
--run' wld _ (Sample d) = lift $ (wld, ) <$> d
--run' (World _ wid) _ (Send (SendRef (RealRef _ wid') _) _)
--  | wid /= wid' = MaybeT $ return Nothing
--run' wld@(World xs _) from (Send (SendRef to@(RealRef idx _) func) m) = do
--  dyns <- MaybeT $ return $ safeIdx xs idx
--  st <- MaybeT $ return $ fromDynamic dyns
--  let action = func (st, from, m)
--  (World xs' wid', (st', y)) <- run' wld (Ref to) action
--  xs'' <- MaybeT $ return $ safeWriteIdx xs' idx (toDyn st')
--  return (World xs'' wid', y)
--    -- Note: This could cause a re-entrancy style bug!
--run' wld _ (Create (Functionality st a)) =
--  let (wld', from') = new wld st
--   in run' wld' from' a
--run' wld from (Compose a f) = do
--  (wld', b) <- run' wld from a
--  run' wld' from (f b)
