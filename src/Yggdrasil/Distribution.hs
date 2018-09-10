{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

-- | Provides primitives for high-level cryptographic sampling.
module Yggdrasil.Distribution
  ( Distribution
  , DistributionT(DistributionT, runDistT)
  , Sampler(..)
  , liftDistribution
  , coin
  , uniform
  ) where

import           Control.Monad             (ap, (>=>))
import           Control.Monad.Trans.Class (MonadTrans (lift))
import           Crypto.Random             (SystemDRG, randomBytesGenerate)
import           Data.Bits                 ((.&.))
import qualified Data.ByteArray            as B
import           Data.Functor.Identity     (Identity (Identity), runIdentity)
import           Data.Maybe                (fromJust)

-- | Allows randomly sampling elements of type @b@.
type Distribution = DistributionT Identity

-- | Allows randomly sampling elements of type @b@ in the context of monad @m@.
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

-- | Provides randomness.
class Sampler s
  where
  -- | Produce a bit of randomness.
  sampleCoin :: s -> (Bool, s)
  -- | Samples a distribution.
  sample :: s -> DistributionT m b -> m (b, s)
  sample s d = runDistT d s
  -- | Samples a distribution, discarding the result randomness.
  sample' :: Monad m => s -> DistributionT m b -> m b
  sample' s d = fst <$> sample s d

instance Sampler SystemDRG where
  sampleCoin s = (b .&. 1 == 1, s')
    where
      (ba :: B.Bytes, s') = randomBytesGenerate 1 s
        -- fromJust is safe, as the array is not empty.
      (b, _) = fromJust $ B.uncons ba

-- | Lifts a 'Distribution' to an arbitrary monadic 'DistributionT'.
liftDistribution :: Monad m => Distribution b -> DistributionT m b
liftDistribution d = DistributionT $ return . runIdentity . runDistT d

-- | Tosses a fair coin.
coin :: Distribution Bool
coin = DistributionT (Identity . sampleCoin)

-- | A uniform 'Distribution' over all elements of @[a]@.
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
