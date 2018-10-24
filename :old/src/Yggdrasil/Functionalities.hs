{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

-- | A collection of common functionalities, ready for use.
module Yggdrasil.Functionalities
  ( ROState
  , SigState
  , commonRandomString
  , randomOracle
  , signature
  ) where

import           Control.Monad.State.Lazy  (get, modify, put)
import           Control.Monad.Trans.Class (lift)

import           Yggdrasil.Adversarial     (WithAdversary' (WithAdversary'))
import           Yggdrasil.Distribution    (Distribution)
import           Yggdrasil.ExecutionModel  (Action (Sample),
                                            ForceSample (forceSample),
                                            Functionality (Functionality),
                                            Interfaces, Operation, Operations)
import           Yggdrasil.HList           (HList ((:::), Nil))
import Yggdrasil.Nat (Zn)

crsOp :: Distribution b -> Operation s (Maybe b) () b
crsOp d () =
  get >>= \case
    Just x -> return x
    Nothing -> do
      x <- lift $ Sample d
      put $ Just x
      return x

-- | A CRS functionality over a given distribution.
commonRandomString :: Distribution b -> Functionality s (Maybe b) '[ '( (), b)]
commonRandomString d = Functionality Nothing (crsOp d ::: Nil)

-- | The state of a 'randomOracle'. Consists of previously recorded
-- query/response pairs.
type ROState a b = [(a, b)]

roLookup :: Eq a => a -> ROState a b -> Maybe b
roLookup _ [] = Nothing
roLookup x' ((x, y):_)
  | x == x' = Just y
roLookup x (_:xs) = roLookup x xs

roOp :: Eq a => Distribution b -> Operation s (ROState a b) a b
roOp d x =
  (roLookup x <$> get) >>= \case
    Just y -> return y
    Nothing -> do
      y <- lift $ Sample d
      modify ((x, y) :)
      return y

-- | A random oracle functionality, over a given distribution.
randomOracle ::
     Eq a => Distribution b -> Functionality s (ROState a b) '[ '( a, b)]
randomOracle d = Functionality [] (roOp d ::: Nil)

-- | The state of a 'signature' functionality. Consists of previously recorded
-- signatures, and their corresponding messages and signers.
type SigState s n msg sig = [(Zn n, (msg, sig))]

verifyOp ::
     (Eq msg, Eq sig) => Operation s (SigState s n msg sig) (Zn n, (msg, sig)) Bool
verifyOp s = (s `elem`) <$> get

fixAdv ::
     (Eq msg, Eq sig, ForceSample sig)
  => HList (Interfaces s '[ '( (Zn n, msg), Maybe sig)])
  -> HList (Operations s (SigState s n msg sig) '[ '( (Zn n, msg), sig)])
fixAdv (sign ::: Nil) = sign' ::: Nil
  where
    sign' (p, msg) = do
      sig <-
        lift (sign (p, msg)) >>= \case
          Just s -> do
            st <- get
            if (p, (msg, s)) `elem` st
              then forceSample' msg p
              else return s
          Nothing -> forceSample' msg p
      modify ((p, (msg, sig)) :)
      return sig
    forceSample' msg p = do
      sig <- lift forceSample
      st <- get
      -- This may recursive infinitely iff the signature space is too small!
      -- This is a feature, not a bug.
      if (p, (msg, sig)) `elem` st
        then forceSample' msg p
        else return sig

-- | A robust signature functionality.
signature ::
     (Eq msg, Eq sig, ForceSample sig)
  => WithAdversary' s (SigState s n msg sig)
    '[ '( (Zn n, msg), sig)]
    '[ '( (Zn n, msg), sig)
     , '( (Zn n, (msg, sig)), Bool)
     ]
signature =
  WithAdversary'
    fixAdv
    (\(sign ::: Nil) -> Functionality [] (sign ::: verifyOp ::: Nil))
