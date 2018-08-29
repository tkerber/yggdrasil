{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses,
             AllowAmbiguousTypes, TypeFamilies, GADTs, FlexibleContexts,
             ScopedTypeVariables #-}

module Yggdrasil.ExecutionModel (
    GlobalState(..), StrongGlobalState(..), Action(..), Funct(..), run
) where

import Yggdrasil.Distribution
import System.Random
import Data.Dynamic

-- A weak global state is what functionalities themselves get to see.
-- the weakness lies functionalities not being able to create a new instance of
-- it, and therefore all references in it being "safe". (Provided of course,
-- they are not returned into the outside world and used there)
class Eq (WeakRef gs) => GlobalState gs where
    data Ref gs :: * -> * -> * -> *
    data WeakRef gs :: *
    weaken :: Ref gs s a b -> WeakRef gs
    new :: (Typeable s, Typeable a, Typeable b) => gs -> Funct gs s a b -> (gs, Ref gs s a b)
    update :: (Typeable s, Typeable a, Typeable b) => gs -> WeakRef gs -> Ref gs s a b -> a -> Maybe (gs, Action gs b)

-- A strong global state is able to create new instances of itself.
class GlobalState gs => StrongGlobalState gs where
    empty :: gs
    external :: WeakRef gs

data Funct gs s a b = Funct s ((s, (WeakRef gs, a)) -> (s, Action gs b))

data Action gs b where
    Return :: b -> Action gs b
    Abort :: Action gs b
    Sample :: Distribution d b => d -> Action gs b
    Send :: (GlobalState gs, Typeable s, Typeable a, Typeable b) => Ref gs s a b -> a -> Action gs b
    Create :: (GlobalState gs, Typeable s, Typeable a, Typeable b) => Funct gs s a b -> Action gs (Ref gs s a b)
    Compose :: Action gs c -> (c -> Action gs b) -> Action gs b

run :: RandomGen g => StrongGlobalState gs => g -> Action gs b -> Maybe b
run g = fmap snd . run' g empty external

run' :: RandomGen g => GlobalState gs => g -> gs -> WeakRef gs -> Action gs b -> Maybe (gs, b)
run' _ _ _ Abort = Nothing
run' _ gs _ (Return x) = Just (gs, x)
run' g gs _ (Sample d) = Just (gs, (sample g d))
run' g gs from (Send ref m) = do
    (gs', a) <- update gs from ref m
    run' g gs' (weaken ref) a
run' g gs _ (Create f) = Just (new gs f)
run' g gs from (Compose a f) = do
    (gs', b) <- run' g gs from a
    run' g gs' from (f b)

instance Functor (Action gs) where
    fmap f a = a >>= (\x -> pure $ f x)

instance Applicative (Action gs) where
    pure = Return
    f <*> a = f >>= (\f -> fmap f a)

instance Monad (Action gs) where
    a >>= b = Compose a b
