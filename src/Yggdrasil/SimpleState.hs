{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module Yggdrasil.SimpleState (SimpleState) where

import Yggdrasil.ExecutionModel
import Data.Dynamic

type SSFunct s a b = Funct SimpleState s a b
newtype SimpleState = SimpleState [Dynamic]

get :: LegalFunct SimpleState s a b =>
    SimpleState ->
    Ref SimpleState s a b ->
    Maybe (Funct SimpleState s a b)
get (SimpleState []) _ = Nothing
get (SimpleState (x:_)) (SSRef 0) = fromDynamic x
get (SimpleState (_:xs)) ref = get (SimpleState xs) (refdec ref)
set :: LegalFunct SimpleState s a b =>
    SimpleState ->
    Ref SimpleState s a b ->
    Funct SimpleState s a b ->
    Maybe SimpleState
set (SimpleState []) _ _ = Nothing
set (SimpleState (_:xs)) (SSRef 0) f = Just $ SimpleState $ toDyn f : xs
set (SimpleState (x:xs)) ref f = do
    SimpleState (xs') <- set (SimpleState xs) (refdec ref) f
    return $ SimpleState (x:xs')
update' :: LegalFunct SimpleState s a b =>
    SimpleState ->
    WeakRef SimpleState ->
    Ref SimpleState s a b ->
    a ->
    Maybe (SimpleState, Action SimpleState b)
update' gs from to msg = get gs to >>= (\(Funct st f) ->
    let (st', a) = f (st, (from, msg)) in
        set gs to (Funct st' f) >>= (\gs' -> return (gs', a)))

refdec :: Ref SimpleState s a b -> Ref SimpleState s a b
refdec (SSRef i) = SSRef (i-1)

instance GlobalState SimpleState where
    data Ref SimpleState s a b = SSRef Int
    data WeakRef SimpleState = SSWeakRef Int deriving Eq
    weaken (SSRef i) = SSWeakRef i
    new (SimpleState xs) f = (SimpleState (xs ++ [toDyn f]), SSRef (length xs))
    update = update'

instance StrongGlobalState SimpleState where
    empty = SimpleState []
    external = SSWeakRef (-1)

