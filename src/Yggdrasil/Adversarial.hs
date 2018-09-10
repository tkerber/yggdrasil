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

-- | Exposes type for reasoning about adversaries. Generally speaking, a
-- 'Functionality' may request interfaces from an 'Adversary', which need to be
-- supplied for it to run. The adversary also exposes some power to the
-- environment to arbitrarily control these interfaces. Functionalities should
-- be aware that the adversary may respond with anything correctly typed, and
-- is explicitly permitted to returning 'Nothing'. 'WithAdversary'' provides
-- an interface to repair unacceptable responses before the functionality
-- itself is called.
module Yggdrasil.Adversarial
  ( Adversary
  , MaybeMap
  , WithAdversary
  , WithAdversary'(..)
  , NoAdversary(..)
  , DummyInterfaces
  , DummyAdversary(..)
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

-- | Maps a list of @'(in, out)@ type tuples to @'(in, 'Maybe' out)@.
type family MaybeMap (bs :: [(*, *)]) = (ys :: [(*, *)]) | ys -> bs where
  MaybeMap '[] = '[]
  MaybeMap ('( a, b) ': xs) = '( a, Maybe b) ': MaybeMap xs

-- | Allows construction of @b@ given a list of interfaces @ts@ from the
-- adversary. The adversarial interfaces return 'Maybe's on all interfaces.
newtype WithAdversary s (ts :: [(*, *)]) b =
  WithAdversary (HList (Interfaces s (MaybeMap ts)) -> b)

-- | Allows construction of a 'Functionality' with state @c@ and interface @bs@
-- whjen given a list of interfaces @as@ from the adversary. The adversarial
-- interface is corrected, by passing it through a filter ensuring valid
-- responses.
data WithAdversary' s c (as :: [(*, *)]) (bs :: [(*, *)]) =
  WithAdversary' (HList (Interfaces s (MaybeMap as)) -> HList (Operations s c as))
                 (HList (Operations s c as) -> Functionality s c bs)

-- | An adversary is a functionality that exposes some interfaces to the
-- environment, and some interfaces returning 'Maybe's to some other party.
type Adversary s c as bs = Functionality s c (as +|+ MaybeMap bs)

-- | The empty adversary returns 'Nothing'.
class NoAdversary s (bs :: [(*, *)]) where
  nullOperations :: HList (Operations s () (MaybeMap bs))
  noAdversary :: Adversary s () '[] bs
  noAdversary = Functionality () (nullOperations @s @bs)

instance NoAdversary s '[] where
  nullOperations = Nil

instance NoAdversary s xs => NoAdversary s ('( a, b) ': xs) where
  nullOperations = (\_ _ -> return Nothing) ::: nullOperations @s @xs

-- | Closely corresponding to 'Interfaces', but also receiving a reference to
-- the original sender.
type family DummyInterfaces s (xs :: [(*, *)]) = (ys :: [*]) | ys -> xs where
  DummyInterfaces s '[] = '[]
  DummyInterfaces s ('( a, b) ': xs) = (Ref s -> a -> Action s b) ': DummyInterfaces s xs

-- | A dummy adversary executes the interfaces the environments hands it.
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

-- | Creates an adversarial functionality given a suitable adversary.
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
