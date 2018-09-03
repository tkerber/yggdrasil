{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Yggdrasil.Functionalities (
    ROState, SigState, SignatureInterface(..), commonRandomString,
    randomOracle, signature, robustSignature
) where

import Data.Dynamic
import Data.Maybe
import Yggdrasil.Adversarial
import Yggdrasil.ExecutionModel
import Yggdrasil.Distribution

crsOp :: Distribution b -> Operation (Maybe b) () b
crsOp _ (Just x, _, ()) = return (Just x, x)
crsOp d (Nothing, _, ()) = (\x -> (Just x, x)) <$> doSample d
commonRandomString :: Typeable b =>
    Distribution b -> Functionality (Maybe b) (() ->> b)
commonRandomString d = Functionality Nothing (interface $ crsOp d)

type ROState a b = [(a, b)]
roLookup :: Eq a => ROState a b -> a -> Maybe b
roLookup [] _ = Nothing
roLookup ((x, y):_) x' | x == x' = Just y
roLookup (_:xs) x = roLookup xs x
roOp :: Eq a => Distribution b -> Operation (ROState a b) a b
roOp d (xs, _, x') = case roLookup xs x' of
    Just y -> return (xs, y)
    Nothing -> do
        y <- doSample d
        return ((x', y):xs, y)
randomOracle :: (Eq a, Typeable a, Typeable b) =>
    Distribution b -> Functionality (ROState a b) (a ->> b)
randomOracle d = Functionality [] (interface $ roOp d)

-- TODO: Don't abort with bad adversaries? Would probably need a specialised s
-- though.
type SigState m s = [(m, s, WeakRef)]
data SignatureInterface m s = SignatureInterface
    { sign :: m ->> s
    , verify :: (m, s, WeakRef) ->> Bool
    }
signOp :: Eq s => ((m, WeakRef) ->> s) -> Operation (SigState m s) m s
signOp adv (st, from, m) = do
    sig <- adv <<- (m, from)
    if any (== sig) (map (\(_, s, _) -> s) st)
       then abort
       else return ((m, sig, from):st, sig)
verifyOp :: (Eq m, Eq s) => Operation (SigState m s) (m, s, WeakRef) Bool
verifyOp (st, _, s) = return $ (st, s `elem` st)
signature :: (Eq m, Eq s, Typeable m, Typeable s) =>
    WithAdversary ((m, WeakRef) ->> s)
        (Functionality (SigState m s) (SignatureInterface m s))
signature adv = Functionality [] (do
    adv' <- adv <<- ()
    adv'' <- fromMaybe abort (return <$> adv')
    sign' <- interface $ signOp adv''
    verify' <- interface $ verifyOp
    return $ SignatureInterface sign' verify')

robustSignOp :: Maybe ((m, WeakRef) ->> [Bool]) -> Int ->
    Operation (SigState m [Bool]) m [Bool]
robustSignOp (Just adv) secparam (st, from, m) = do
    sig <- adv <<- (m, from)
    sig' <- if any (== sig) (map (\(_, s, _) -> s) st)
        then forceSample secparam
        else return sig
    return ((m, sig', from):st, sig')
robustSignOp Nothing secparam (st, from, m) =
    (\sig -> ((m, sig, from):st, sig)) <$> forceSample secparam
forceSample :: Int -> Action [Bool]
forceSample secparam = sequence [doSample coin | _ <- [0..secparam]]
robustSignature :: (Eq m, Typeable m) =>
    Int -> WithAdversary ((m, WeakRef) ->> [Bool])
        (Functionality (SigState m [Bool]) (SignatureInterface m [Bool]))
robustSignature secparam adv = Functionality [] (do
    adv' <- adv <<- ()
    sign' <- interface $ robustSignOp adv' secparam
    verify' <- interface $ verifyOp
    return $ SignatureInterface sign' verify')
