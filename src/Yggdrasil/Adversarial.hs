{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Yggdrasil.Adversarial (
    WithAdversary, Adversary, createAdversarial, noAdversary, dummyAdversary
) where

import Data.Dynamic
import Yggdrasil.ExecutionModel

type WithAdversary b c = (() ->> Maybe b) -> c

type Adversary s a b = Functionality s (() ->> Maybe a, b)

-- | An adversary that just returns 'Nothing'.
noAdversary :: Adversary () a ()
noAdversary = Functionality ()
    ((,()) <$> interface (\_ -> return ((), Nothing)))

-- | An adversary that simply forwards a reference to the environment
dummyAdversary :: (() ->> Maybe b) -> Adversary () b ()
dummyAdversary ref = Functionality () (return (ref, ()))

-- | Given an adversary, and a functionality that requires one, link the two
-- and return their respective handles.
createAdversarial :: (Typeable s, Typeable s') =>
    Adversary s a c -> WithAdversary a (Functionality s' b) -> Action (b, c)
createAdversarial adv fnc = do
    (advFnc, advEnv) <- create adv
    fncEnv <- create $ fnc advFnc
    return (fncEnv, advEnv)
