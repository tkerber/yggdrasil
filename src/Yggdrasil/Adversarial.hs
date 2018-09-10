{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE ExplicitNamespaces     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}

module Yggdrasil.Adversarial
  ( Adversary
  , WithAdversary
  , WithAdversary'(..)
  , NoAdversary(noAdversary)
  , DummyInterfaces
  , DummyAdversary(dummyAdversary)
  , CreateAdversarial(..)
  ) where

import           Control.Arrow             (second)
import           Control.Monad.Trans.Class (lift)
import           Yggdrasil.ExecutionModel  (Action (Create),
                                            Functionality (Functionality),
                                            InterfaceMap, Interfaces, Operation,
                                            Operations, Ref)
import           Yggdrasil.HList           (type (+|+), HList ((:::), Nil),
                                            HSplit (hsplit))

type family MaybeMap (bs :: [(*, *)]) = (ys :: [(*, *)]) | ys -> bs where
  MaybeMap '[] = '[]
  MaybeMap ('( a, b) ': xs) = '( a, Maybe b) ': MaybeMap xs

newtype WithAdversary s (ts :: [(*, *)]) b =
  WithAdversary (HList (Interfaces s (MaybeMap ts)) -> b)

data WithAdversary' s c (as :: [(*, *)]) (bs :: [(*, *)]) =
  WithAdversary' (HList (Interfaces s (MaybeMap as)) -> HList (Operations s c as))
                 (HList (Operations s c as) -> Functionality s c bs)

type Adversary s c as bs = Functionality s c (as +|+ MaybeMap bs)

class NoAdversary s (bs :: [(*, *)]) where
  nullOperations :: HList (Operations s () (MaybeMap bs))
  noAdversary :: Adversary s () '[] bs
  noAdversary = Functionality () (nullOperations @s @bs)

instance NoAdversary s '[] where
  nullOperations = Nil

instance NoAdversary s xs => NoAdversary s ('( a, b) ': xs) where
  nullOperations = (\_ _ -> return Nothing) ::: nullOperations @s @xs

type family DummyInterfaces s (xs :: [(*, *)]) = (ys :: [*]) | ys -> xs where
  DummyInterfaces s '[] = '[]
  DummyInterfaces s ('( a, b) ': xs) = (Ref s -> a -> Action s b) ': DummyInterfaces s xs

class DummyAdversary s (bs :: [(*, *)]) where
  operations ::
       HList (DummyInterfaces s (MaybeMap bs))
    -> HList (Operations s () (MaybeMap bs))
  dummyAdversary ::
       HList (DummyInterfaces s (MaybeMap bs)) -> Adversary s () '[] bs
  dummyAdversary = Functionality () . operations @s @bs

instance DummyAdversary s '[] where
  operations _ = Nil

instance DummyAdversary s bs => DummyAdversary s ('( a, b) ': bs) where
  operations (b ::: bs) =
    ((\ref x -> lift $ b ref x) :: Operation s () a (Maybe b)) :::
    operations @s @bs bs

class CreateAdversarial s c as bs adv b where
  createAdversarial ::
       ( HSplit (Interfaces s (as +|+ MaybeMap bs)) (Interfaces s as) (Interfaces s (MaybeMap bs))
       , InterfaceMap s c (as +|+ MaybeMap bs)
       )
    => Adversary s c as bs
    -> adv
    -> Action s (HList (Interfaces s as), b)

instance CreateAdversarial s c as bs (WithAdversary s bs b) b where
  createAdversarial adv (WithAdversary f) = second f . hsplit <$> Create adv

instance CreateAdversarial s c as bs (WithAdversary' s c bs cs) (Functionality s c cs) where
  createAdversarial adv (WithAdversary' g f) =
    (\(a, b) -> (a, f (g b))) . hsplit <$> Create adv
