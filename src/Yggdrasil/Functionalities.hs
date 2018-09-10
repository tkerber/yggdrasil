{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

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
                                            Interfaces, Operation, Operations,
                                            Ref)
import           Yggdrasil.HList           (HList ((:::), Nil))

crsOp :: Distribution b -> Operation s (Maybe b) () b
crsOp d _ () =
  get >>= \case
    Just x -> return x
    Nothing -> do
      x <- lift $ Sample d
      put $ Just x
      return x

commonRandomString :: Distribution b -> Functionality s (Maybe b) '[ '( (), b)]
commonRandomString d = Functionality Nothing (crsOp d ::: Nil)

type ROState a b = [(a, b)]

roLookup :: Eq a => a -> ROState a b -> Maybe b
roLookup _ [] = Nothing
roLookup x' ((x, y):_)
  | x == x' = Just y
roLookup x (_:xs) = roLookup x xs

roOp :: Eq a => Distribution b -> Operation s (ROState a b) a b
roOp d _ x =
  (roLookup x <$> get) >>= \case
    Just y -> return y
    Nothing -> do
      y <- lift $ Sample d
      modify ((x, y) :)
      return y

randomOracle ::
     Eq a => Distribution b -> Functionality s (ROState a b) '[ '( a, b)]
randomOracle d = Functionality [] (roOp d ::: Nil)

type SigState s msg sig = [(msg, sig, Ref s)]

verifyOp ::
     (Eq msg, Eq sig) => Operation s (SigState s msg sig) (msg, sig, Ref s) Bool
verifyOp _ s = (s `elem`) <$> get

fixAdv ::
     (Eq msg, Eq sig, ForceSample sig)
  => HList (Interfaces s '[ '( (msg, Ref s), Maybe sig)])
  -> HList (Operations s (SigState s msg sig) '[ '( (msg, Ref s), sig)])
fixAdv (sign ::: Nil) = sign' ::: Nil
  where
    sign' _ (msg, ref) = do
      sig <-
        lift (sign (msg, ref)) >>= \case
          Just s -> do
            st <- get
            if (msg, s, ref) `elem` st
              then forceSample' msg ref
              else return s
          Nothing -> forceSample' msg ref
      modify ((msg, sig, ref) :)
      return sig
    forceSample' msg ref = do
      sig <- lift forceSample
      st <- get
      -- This may recursive infinitely iff the signature space is too small!
      -- This is a feature, not a bug.
      if (msg, sig, ref) `elem` st
        then forceSample' msg ref
        else return sig

signature ::
     (Eq msg, Eq sig, ForceSample sig)
  => WithAdversary' s (SigState s msg sig)
    '[ '( (msg, Ref s), sig)]
    '[ '( (msg, Ref s), sig)
     , '( (msg, sig, Ref s), Bool)
     ]
signature =
  WithAdversary'
    fixAdv
    (\(sign ::: Nil) -> Functionality [] (sign ::: verifyOp ::: Nil))
