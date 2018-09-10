{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FunctTests
  ( spec
  ) where

import           Crypto.Random             (getSystemDRG)
import           Test.Hspec                (Spec, describe, it, shouldBe)
import           Yggdrasil.Distribution    (sample', uniform)
import           Yggdrasil.ExecutionModel  (Action (Create), run)
import           Yggdrasil.Functionalities (commonRandomString, randomOracle)
import           Yggdrasil.HList           (HList ((:::), Nil))

crsSameTest :: Action s Bool
crsSameTest = do
  (crsHandle ::: Nil) <-
    Create $ commonRandomString (uniform [0 .. 10000 :: Int])
  fst' <- crsHandle ()
  snd' <- crsHandle ()
  return (fst' == snd')

roSameTest :: Action s Bool
roSameTest = do
  ((roHandle :: Int -> Action s Int) ::: Nil) <-
    Create $ randomOracle (uniform [0 .. 1000 :: Int])
  fst' <- roHandle 1
  snd' <- roHandle 1
  return (fst' == snd')

roAllEqual :: Action s Bool
roAllEqual = do
  ((roHandle :: Int -> Action s Int) ::: Nil) <-
    Create $ randomOracle (uniform [0 .. 1000 :: Int])
  xs <- sequence [roHandle i | i <- [1 .. 1000]]
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
