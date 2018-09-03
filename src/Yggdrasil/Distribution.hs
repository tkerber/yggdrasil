{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Yggdrasil.Distribution (
    Distribution, Sampler, sample, sample', coin, uniform
) where

import Control.Monad (ap)
import Crypto.Random (SystemDRG, randomBytesGenerate)
import Data.Bits ((.&.))
import Data.Maybe (fromJust)
import qualified Data.ByteArray as B

newtype Distribution b = Distribution (forall s. Sampler s => s -> (b, s))

instance Functor Distribution where
    fmap f x = pure f <*> x
instance Applicative Distribution where
    pure x = Distribution (x,)
    (<*>) = ap
instance Monad Distribution where
    a >>= b = Distribution (\s -> let
            (a', s') = sample s a
            (b', s'') = sample s' (b a')
        in (b', s''))

class Sampler s where
    sampleCoin :: s -> (Bool, s)

instance Sampler SystemDRG where
    sampleCoin s = (b .&. 1 == 1, s')
      where
        (ba :: B.Bytes, s') = randomBytesGenerate 1 s
        -- fromJust is safe, as the array is not empty.
        (b, _) = fromJust $ B.uncons ba

sample :: Sampler s => s -> Distribution b -> (b, s)
sample s (Distribution f) = f s

sample' :: Sampler s => s -> Distribution b -> b
sample' s = fst . sample s

coin :: Distribution Bool
coin = Distribution sampleCoin

uniform :: [a] -> Distribution a
uniform xs = do
    let l = length xs
    let lg = ilog2 l
    n <- samplen lg
    if n > l then uniform xs else return (xs !! n)
  where
    ilog2 :: Int -> Int
    ilog2 1 = 0
    ilog2 n | n > 1 = ilog2 (n `div` 2) + 1
    ilog2 _ = error "attempted non-postive logarithm"
    samplen :: Int -> Distribution Int
    samplen 0 = return 0
    samplen lg | lg > 0 = do
        n' <- samplen (lg-1)
        c <- coin 
        return $ (n' * 2) + if c then 1 else 0
    samplen _ = error "attempted to sample negative logarithm"
