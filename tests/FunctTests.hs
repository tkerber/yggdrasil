{-# LANGUAGE ScopedTypeVariables,
             TypeOperators #-}

module FunctTests (spec) where

import Crypto.Random
import Test.Hspec
import Yggdrasil.ExecutionModel
import Yggdrasil.Distribution
import Yggdrasil.Functionalities

crsSameTest :: Action Bool
crsSameTest = do
    crsHandle <- create $ commonRandomString (uniform [0..10000::Int])
    fst' <- () ->> crsHandle
    snd' <- () ->> crsHandle
    return (fst' == snd')

roSameTest :: Action Bool
roSameTest = do
    roHandle :: (Int ->> Int) <- create $ randomOracle (uniform [0..1000::Int])
    fst' <- 1 ->> roHandle
    snd' <- 1 ->> roHandle
    return (fst' == snd')

roAllEqual :: Action Bool
roAllEqual = do
    roHandle :: (Int ->> Int) <- create $ randomOracle (uniform [0..1000::Int])
    xs <- sequence [i ->> roHandle | i <- [1..1000]]
    return $ and $ map (== head xs) (tail xs)

spec :: IO Spec
spec = do
    rnd <- getSystemDRG
    return $ do
        describe "common random string" $ do
            it "returns the same value" $
                (fmap fst (run rnd crsSameTest)) `shouldBe` Just True
        describe "random oracle" $ do
            it "returns the same for the same query" $
                (fmap fst (run rnd roSameTest)) `shouldBe` Just True
            it "is random with different queries" $
                (fmap fst (run rnd roAllEqual)) `shouldBe` Just False
