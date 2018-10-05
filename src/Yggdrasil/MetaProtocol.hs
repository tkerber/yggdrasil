{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Yggdrasil.MetaProtocol
  ( MetaProtocol
  , Relay
  , npartyIdeal
  , npartyReal
  ) where

import           Control.Monad.State.Lazy  (get, put)
import           Control.Monad.Trans.Class (lift)
import           Yggdrasil.ExecutionModel  (Action (Create),
                                            Functionality (Functionality),
                                            InterfaceMap, Interfaces,
                                            Operations)
import           Yggdrasil.HList           (HList ((:::), Nil))

type MetaProtocol s c c' ops ops'
   = Functionality s c ops -> Functionality s c' ops'

class Relay s (ops :: [(*, *)]) where
  operations :: (HList (Interfaces s ops)) -> (HList (Operations s () ops))
  relay :: (HList (Interfaces s ops)) -> Functionality s () ops
  relay is = Functionality () (operations @s @ops is)

instance Relay s '[] where
  operations _ = Nil

instance Relay s xs => Relay s ('( a, b) ': xs) where
  operations (f ::: xs) = lifted ::: operations @s @xs xs
    where
      lifted _ a = lift (f a)

npartyIdeal ::
     (InterfaceMap s c ops, InterfaceMap s () ops, Relay s ops)
  => Integer
  -> MetaProtocol s c (Maybe [HList (Interfaces s ops)]) ops '[ '( (), [HList (Interfaces s ops)])]
npartyIdeal n f = Functionality Nothing (mkOp ::: Nil)
  where
    mkOp _ _ =
      get >>= \case
        Just i -> return i
        Nothing -> do
          f0 <- lift $ Create f
          is <- (lift . sequence) [Create (relay f0) | _ <- [1 .. n]]
          put (Just is)
          return is

npartyReal ::
     (InterfaceMap s c ops)
  => Integer
  -> MetaProtocol s c (Maybe [HList (Interfaces s ops)]) ops '[ '( (), [HList (Interfaces s ops)])]
npartyReal n f = Functionality Nothing (mkOp ::: Nil)
  where
    mkOp _ _ =
      get >>= \case
        Just i -> return i
        Nothing -> do
          is <- (lift . sequence) [Create f | _ <- [1 .. n]]
          put (Just is)
          return is
