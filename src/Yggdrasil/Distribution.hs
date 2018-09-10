{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Yggdrasil.Distribution
  ( Distribution(Distribution)
  , DistributionT(DistributionT, runDistT)
  , Sampler
  , sample
  , sample'
  , coin
  , uniform
  , liftDistribution
  ) where

import           Control.Monad             (ap, (>=>))
import           Control.Monad.State.Lazy  (State, runState, state)
import           Control.Monad.Trans.Class (MonadTrans (lift))
import           Crypto.Random             (SystemDRG, randomBytesGenerate)
import           Data.Bits                 ((.&.))
import qualified Data.ByteArray            as B
import           Data.Maybe                (fromJust)

newtype Distribution b =
  Distribution (forall s. Sampler s =>
                            State s b)

instance Functor Distribution where
  fmap f x = pure f <*> x

instance Applicative Distribution where
  pure x = Distribution $ state (x, )
  (<*>) = ap

instance Monad Distribution where
  a >>= b =
    Distribution $
    state
      (\s ->
         let (a', s') = sample s a
             (b', s'') = sample s' (b a')
          in (b', s''))

newtype DistributionT m b = DistributionT
  { runDistT :: forall s. Sampler s =>
                            s -> m (b, s)
  }

instance Monad m => Functor (DistributionT m) where
  fmap f x = pure f <*> x

instance Monad m => Applicative (DistributionT m) where
  pure x = DistributionT $ pure . (x, )
  (<*>) = ap

instance Monad m => Monad (DistributionT m) where
  a >>= b = DistributionT $ runDistT a >=> (\(a', s') -> runDistT (b a') s')

instance MonadTrans DistributionT where
  lift m = DistributionT $ \s -> (, s) <$> m

liftDistribution :: Monad m => Distribution b -> DistributionT m b
liftDistribution d = DistributionT $ \s -> return $ sample s d

class Sampler s where
  sampleCoin :: s -> (Bool, s)

instance Sampler SystemDRG where
  sampleCoin s = (b .&. 1 == 1, s')
    where
      (ba :: B.Bytes, s') = randomBytesGenerate 1 s
        -- fromJust is safe, as the array is not empty.
      (b, _) = fromJust $ B.uncons ba

sample :: Sampler s => s -> Distribution b -> (b, s)
sample s (Distribution st) = runState st s

sample' :: Sampler s => s -> Distribution b -> b
sample' s = fst . sample s

coin :: Distribution Bool
coin = Distribution $ state sampleCoin

uniform :: [a] -> Distribution a
uniform xs = do
  let l = length xs
  let lg = ilog2 l
  n <- samplen lg
  if n > l
    then uniform xs
    else return (xs !! n)
  where
    ilog2 :: Int -> Int
    ilog2 1 = 0
    ilog2 n
      | n > 1 = ilog2 (n `div` 2) + 1
    ilog2 _ = error "attempted non-postive logarithm"
    samplen :: Int -> Distribution Int
    samplen 0 = return 0
    samplen lg
      | lg > 0 = do
        n' <- samplen (lg - 1)
        c <- coin
        return $
          (n' * 2) +
          if c
            then 1
            else 0
    samplen _ = error "attempted to sample negative logarithm"
