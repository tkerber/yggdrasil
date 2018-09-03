{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module FunctTests (spec) where

import Crypto.Random
import Test.Hspec
import Yggdrasil.ExecutionModel
import Yggdrasil.Distribution
import Yggdrasil.Functionalities

crsSameTest :: Action Bool
crsSameTest = do
    crsHandle <- create commonRandomString (uniform [0..10000::Int])
    fst' <- () ->> crsHandle
    snd' <- () ->> crsHandle
    return (fst' == snd')

roSameTest :: Action Bool
roSameTest = do
    roHandle :: (Int ->> Int) <- create randomOracle (uniform [0..1000::Int])
    fst' <- 1 ->> roHandle
    snd' <- 1 ->> roHandle
    return (fst' == snd')

roAllEqual :: Action Bool
roAllEqual = do
    roHandle :: (Int ->> Int) <- create randomOracle (uniform [0..1000::Int])
    xs <- sequence [i ->> roHandle | i <- [1..1000]]
    return $ all (== head xs) (tail xs)

spec :: IO Spec
spec = do
    rnd <- getSystemDRG
    return $ do
        describe "common random string" $
            it "returns the same value" $
                sample' rnd (run crsSameTest) `shouldBe` Just True
        describe "random oracle" $ do
            it "returns the same for the same query" $
                sample' rnd (run roSameTest) `shouldBe` Just True
            it "is random with different queries" $
                sample' rnd (run roAllEqual) `shouldBe` Just False