
module Yggdrasil.Functionalities (
    commonRandomString, randomOracle
) where

import Data.Dynamic
import Yggdrasil.ExecutionModel
import Yggdrasil.Distribution

type CRSState b = Maybe b
crsOp :: Distribution b -> Operation (CRSState b) () b
crsOp _ ((Just x), _, ()) = return (Just x, x)
crsOp d (Nothing, _, ()) = fmap (\x -> (Just x, x)) $ doSample d 
commonRandomString :: Typeable b =>
    Distribution b -> Functionality (CRSState b) (Ref (CRSState b) () b)
commonRandomString d = Functionality Nothing (strengthenSelf (crsOp d))

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
    Distribution b -> Functionality (ROState a b) (Ref (ROState a b) a b)
randomOracle d = Functionality [] (strengthenSelf (roOp d))
