module Yggdrasil.Distribution

import Control.Monad.Identity
import Yggdrasil.Zn

public export
interface Sampler s where
  sampleZn : {n : Nat} -> s -> (Zn (S n), s)

export
data DistributionT : (Type -> Type) -> Type -> Type where
  MkDistributionT : {a : Type} ->
                    ({s : Type} -> Sampler s => s -> m (Pair a s)) ->
                    DistributionT m a

export
Distribution : Type -> Type
Distribution = DistributionT Identity

Functor f => Functor (DistributionT f) where
  map g (MkDistributionT d) = MkDistributionT
    (\s => map (\(a, s) => (g a, s)) (d s))

-- We actually need a Monad here already. Rationale: Since we need the same
-- sampler for `f` and `x`, and we don't want reuse, we need the `bind` to
-- reduce the two-layered applicative to one.
Monad m => Applicative (DistributionT m) where
  pure x = MkDistributionT (\s => pure (x, s))
  (MkDistributionT fa) <*> (MkDistributionT xa) = MkDistributionT (\s => do
    (f, s') <- fa s
    (x, s'') <- xa s'
    pure (f x, s''))

Monad m => Monad (DistributionT m) where
  (MkDistributionT a) >>= b = MkDistributionT (\s =>
    a s >>= (\(a', s') => let (MkDistributionT b') = (b a') in b' s'))

export
coin : Distribution Bool
coin = map toBool $ MkDistributionT (Id . sampleZn)

distZn : {n : Nat} -> Distribution (Zn (S n))
distZn = MkDistributionT (Id . sampleZn)

export
liftDistribution : Monad m => Distribution b -> DistributionT m b
liftDistribution (MkDistributionT d) = MkDistributionT $ pure . runIdentity . d

export
uniform : (l : List a) -> {auto ok : NonEmpty l} -> Distribution a
uniform (x::xs) = map (indexZn (x::xs)) (distZn {n=length xs})
