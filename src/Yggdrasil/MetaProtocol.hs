{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}

module Yggdrasil.MetaProtocol
  ( MetaProtocol
  , RelayN
  , npartyIdeal
  , npartyReal
  ) where

import           Control.Monad.State.Lazy  (get, put)
import           Control.Monad.Trans.Class (lift)
import           Yggdrasil.ExecutionModel  (Action (Create),
                                            Functionality (Functionality),
                                            InterfaceMap, Interfaces,
                                            Operations)
import           Yggdrasil.HList           (HList ((:::), Nil),
                                            HSequence (hsequence))
import           Yggdrasil.Nat             (ForEach, ForEach (foreach),
                                            IdApplied (idApplied), NCopies, Zn)

type MetaProtocol s c c' ops ops'
   = Functionality s c ops -> Functionality s c' ops'

class RelayN s n (ops :: [(*, *)]) where
  relayNOperations ::
       (HList (Interfaces s (WithZn n ops)))
    -> Zn n
    -> (HList (Operations s () ops))
  relayN ::
       (HList (Interfaces s (WithZn n ops))) -> Zn n -> Functionality s () ops
  relayN is n = Functionality () (relayNOperations @s @n @ops is n)

instance RelayN s n '[] where
  relayNOperations _ _ = Nil

instance RelayN s n xs => RelayN s n ('( a, b) ': xs) where
  relayNOperations (f ::: xs) n = lift . f . (n, ) ::: relayNOperations @s @n @xs xs n

type family WithZn n (ops :: [(*, *)]) = (ys :: [(*, *)]) | ys -> ops where
  WithZn n '[] = '[]
  WithZn n ('( a, b) ': xs) = '( (Zn n, a), b) ': WithZn n xs

npartyIdeal ::
     forall s c n ops.
     ( ForEach n (Action s (HList (Interfaces s ops)))
     , IdApplied (Action s) n (HList (Interfaces s ops))
     , RelayN s n ops
     , InterfaceMap s c (WithZn n ops)
     , InterfaceMap s () ops
     , HSequence (Action s) (NCopies n (HList (Interfaces s ops)))
     )
  => MetaProtocol s c
    (Maybe (HList (NCopies n (HList (Interfaces s ops)))))
    (WithZn n ops)
    '[ '( (), HList (NCopies n (HList (Interfaces s ops))))]
npartyIdeal f = Functionality Nothing (mkOp ::: Nil)
  where
    mkOp _ =
      get >>= \case
        Just i -> return i
        Nothing -> do
          f0 <- lift $ Create f
          is <-
            (lift .
             hsequence . idApplied @(Action s) @n @(HList (Interfaces s ops)))
              (foreach (\i -> Create (relayN @s @n @ops f0 i)))
          put (Just is)
          return is

npartyReal ::
     forall s c n ops.
     ( ForEach n (Action s (HList (Interfaces s ops)))
     , IdApplied (Action s) n (HList (Interfaces s ops))
     , InterfaceMap s c ops
     , HSequence (Action s) (NCopies n (HList (Interfaces s ops)))
     )
  => MetaProtocol s c
    (Maybe (HList (NCopies n (HList (Interfaces s ops)))))
    ops
    '[ '( (), HList (NCopies n (HList (Interfaces s ops))))]
npartyReal f = Functionality Nothing (mkOp ::: Nil)
  where
    mkOp _ =
      get >>= \case
        Just i -> return i
        Nothing -> do
          is <-
            (lift .
             hsequence . idApplied @(Action s) @n @(HList (Interfaces s ops)))
              (foreach (\_ -> Create f))
          put (Just is)
          return is
