{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeOperators #-}

module Yggdrasil.Functionalities
  ( ROState
  --, SigState
  --, SignatureInterface(..)
  , commonRandomString
  , randomOracle
  --, signature
  --, robustSignature
  ) where

import           Control.Monad.State.Lazy  (get, modify, put)
import           Control.Monad.Trans.Class (lift)

--import           Yggdrasil.Adversarial    (WithAdversary)
import           Yggdrasil.Distribution    (Distribution)
import           Yggdrasil.ExecutionModel  (Action (Sample),
                                            Functionality (Functionality),
                                            Operation)
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
-- TODO: Don't abort with bad adversaries? Would probably need a specialised s
-- though.
--type SigState m s = [(m, s, Ref)]
--
--data SignatureInterface m s = SignatureInterface
--  { sign   :: m -> Action s
--  , verify :: (m, s, Ref) -> Action Bool
--  }
--
--signOp :: Eq s => ((m, Ref) -> Action s) -> Operation (SigState m s) m s
--signOp adv (st, from, m) = do
--  sig <- adv (m, from)
--  if sig `elem` map (\(_, s, _) -> s) st
--    then abort
--    else return ((m, sig, from) : st, sig)
--
--verifyOp :: (Eq m, Eq s) => Operation (SigState m s) (m, s, Ref) Bool
--verifyOp (st, _, s) = return (st, s `elem` st)
--signature ::
--     (Eq m, Eq s, Typeable m, Typeable s)
--  => WithAdversary ((m, Ref) -> Action s) (Functionality (SigState m s) (SignatureInterface m s))
--signature adv =
--  Functionality
--    []
--    (do adv' <- adv
--        adv'' <- maybe abort return adv'
--    --adv'' <- fromMaybe abort (return <$> adv')
--        sign' <- interface $ signOp adv''
--        verify' <- interface verifyOp
--        return $ SignatureInterface sign' verify')
--
--robustSignOp ::
--     Maybe ((m, Ref) -> Action [Bool])
--  -> Int
--  -> Operation (SigState m [Bool]) m [Bool]
--robustSignOp (Just adv) secparam (st, from, m) = do
--  sig <- adv (m, from)
--  sig' <-
--    if sig `elem` map (\(_, s, _) -> s) st
--      then forceSample secparam
--      else return sig
--  return ((m, sig', from) : st, sig')
--robustSignOp Nothing secparam (st, from, m) =
--  (\sig -> ((m, sig, from) : st, sig)) <$> forceSample secparam
--
--forceSample :: Int -> Action [Bool]
--forceSample secparam = sequence [doSample coin | _ <- [0 .. secparam]]
--
--robustSignature ::
--     (Eq m, Typeable m)
--  => Int
--  -> WithAdversary ((m, Ref) -> Action [Bool]) (Functionality (SigState m [Bool]) (SignatureInterface m [Bool]))
--robustSignature secparam adv =
--  Functionality
--    []
--    (do adv' <- adv
--        sign' <- interface $ robustSignOp adv' secparam
--        verify' <- interface verifyOp
--        return $ SignatureInterface sign' verify')
