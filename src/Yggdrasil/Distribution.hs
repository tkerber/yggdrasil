{-# LANGUAGE MultiParamTypeClasses, ExistentialQuantification, Rank2Types #-}

module Yggdrasil.Distribution (Distribution, sample) where

import Control.Monad
import System.Random

newtype Distribution b = Distribution (forall g. RandomGen g => g -> (b, g))

sample :: RandomGen g => g -> Distribution b -> (b, g)
sample g (Distribution f) = f g

instance Functor Distribution where
    fmap f x = pure f <*> x
instance Applicative Distribution where
    pure x = Distribution (\g -> (x, g))
    (<*>) = ap
instance Monad Distribution where
    a >>= b = Distribution (\g ->
        let (a', g') = sample g a in
        let (b', g'') = sample g' (b a')
        in (b', g''))
