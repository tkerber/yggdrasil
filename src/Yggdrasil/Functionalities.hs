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
import           Yggdrasil.Distribution    (Distribution, coin)
import           Yggdrasil.ExecutionModel  (Action (Sample, SecParam),
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

type SigState s msg = [(msg, [Bool], Ref s)]

verifyOp :: (Eq msg) => Operation s (SigState s msg) (msg, [Bool], Ref s) Bool
verifyOp _ s = (s `elem`) <$> get

forceSample :: Action s [Bool]
forceSample = SecParam >>= (\sp -> sequence [Sample coin | _ <- [0 .. sp]])

fixAdv ::
     Eq msg
  => HList (Interfaces s '[ '( (msg, Ref s), Maybe [Bool])])
  -> HList (Operations s (SigState s msg) '[ '( (msg, Ref s), [Bool])])
fixAdv (sign ::: Nil) = sign' ::: Nil
  where
    sign' _ (msg, ref) =
      lift (sign (msg, ref)) >>=
      (\case
         Just s ->
           get >>=
           (\st ->
              if (msg, s, ref) `elem` st
                then lift forceSample
                else return s)
         Nothing -> lift forceSample) >>=
      (\s -> modify ((msg, s, ref) :) >> return s)

signature ::
     Eq msg
  => WithAdversary' s (SigState s msg)
    '[ '( (msg, Ref s), [Bool])]
    '[
        '( (msg, Ref s), [Bool]),
        '( (msg, [Bool], Ref s), Bool)
     ]
signature =
  WithAdversary'
    fixAdv
    (\(sign ::: Nil) -> Functionality [] (sign ::: verifyOp ::: Nil))
