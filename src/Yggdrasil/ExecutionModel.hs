{-# LANGUAGE TypeFamilies, GADTs, FlexibleContexts, ConstraintKinds #-}

module Yggdrasil.ExecutionModel (
    GlobalState(..), StrongGlobalState(..), Action, Funct(..), LegalFunct, run,
    abort, sample, send, create
) where

import Control.Monad
import Data.Dynamic
import System.Random
import Yggdrasil.Distribution

-- A weak global state is what functionalities themselves get to see.
-- the weakness lies functionalities not being able to create a new instance of
-- it, and therefore all references in it being "safe". (Provided of course,
-- they are not returned into the outside world and used there)
class Eq (WeakRef gs) => GlobalState gs where
    data Ref gs :: * -> * -> * -> *
    data WeakRef gs :: *
    weaken :: Ref gs s a b -> WeakRef gs
    new :: LegalFunct gs s a b => gs -> Funct gs s a b -> (gs, Ref gs s a b)
    update :: LegalFunct gs s a b =>
        gs -> WeakRef gs -> Ref gs s a b -> a -> Maybe (gs, Action gs b)

-- A strong global state is able to create new instances of itself.
class GlobalState gs => StrongGlobalState gs where
    empty :: gs
    external :: WeakRef gs

data Funct gs s a b = Funct s ((s, (WeakRef gs, a)) -> (s, Action gs b))

type LegalFunct gs s a b = (GlobalState gs, Typeable s, Typeable a, Typeable b)

data Action gs b where
    Abort :: Action gs b
    Sample :: Distribution b -> Action gs b
    Send :: LegalFunct gs s a b => Ref gs s a b -> a -> Action gs b
    Create :: LegalFunct gs s a b => Funct gs s a b -> Action gs (Ref gs s a b)
    Compose :: Action gs c -> (c -> Action gs b) -> Action gs b

-- Export visible constructors as functions.
abort :: Action gs b
abort = Abort
doSample :: Distribution b -> Action gs b
doSample = Sample
send :: LegalFunct gs s a b => Ref gs s a b -> a -> Action gs b
send = Send
create :: LegalFunct gs s a b => Funct gs s a b -> Action gs (Ref gs s a b)
create = Create

run :: (RandomGen g, StrongGlobalState gs) => g -> Action gs b -> (Maybe b, g)
run g a = let (r, g') = run' g empty external a in (fmap snd r, g')

run' :: (RandomGen g, GlobalState gs) =>
    g -> gs -> WeakRef gs -> Action gs b -> (Maybe (gs, b), g)
run' g _ _ Abort = (Nothing, g)
run' g gs _ (Sample d) = let (y, g') = sample g d in (Just (gs, y), g')
run' g gs from (Send ref m) = case update gs from ref m of
    Just (gs', a) -> run' g gs' (weaken ref) a
    Nothing -> (Nothing, g)
run' g gs _ (Create f) = (Just (new gs f), g)
run' g gs from (Compose a f) = case run' g gs from a of
    (Just (gs', b), g') -> run' g' gs' from (f b)
    (Nothing, g') -> (Nothing, g')

instance Functor (Action gs) where
    fmap f x = pure f <*> x
instance Applicative (Action gs) where
    pure = Sample . pure
    (<*>) = ap
instance Monad (Action gs) where
    a >>= b = Compose a b
