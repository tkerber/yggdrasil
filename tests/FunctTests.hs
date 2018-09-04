{-# LANGUAGE ScopedTypeVariables #-}

module FunctTests
  ( spec
  ) where

import           Crypto.Random             (getSystemDRG)
import           Test.Hspec                (Spec, describe, it, shouldBe)
import           Yggdrasil.Distribution    (sample', uniform)
import           Yggdrasil.ExecutionModel  (Action, create, run)
import           Yggdrasil.Functionalities (commonRandomString, randomOracle)

crsSameTest :: Action Bool
crsSameTest = do
  crsHandle <- create $ commonRandomString (uniform [0 .. 10000 :: Int])
  fst' <- crsHandle
  snd' <- crsHandle
  return (fst' == snd')

roSameTest :: Action Bool
roSameTest = do
  roHandle :: (Int -> Action Int) <-
    create $ randomOracle (uniform [0 .. 1000 :: Int])
  fst' <- roHandle 1
  snd' <- roHandle 1
  return (fst' == snd')

roAllEqual :: Action Bool
roAllEqual = do
  roHandle :: (Int -> Action Int) <-
    create $ randomOracle (uniform [0 .. 1000 :: Int])
  xs <- sequence [roHandle i | i <- [1 .. 1000]]
  return $ all (== head xs) (tail xs)

spec :: IO Spec
spec = do
  rnd <- getSystemDRG
  let secparam = 128
  return $ do
    describe "common random string" $
      it "returns the same value" $
      sample' rnd (run secparam crsSameTest) `shouldBe` Just True
    describe "random oracle" $ do
      it "returns the same for the same query" $
        sample' rnd (run secparam roSameTest) `shouldBe` Just True
      it "is random with different queries" $
        sample' rnd (run secparam roAllEqual) `shouldBe` Just False
