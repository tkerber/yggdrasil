{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FunctTests
  ( spec
  ) where

import           Crypto.Random             (getSystemDRG)
import           Test.Hspec                (Spec, describe, it, shouldBe)
import           Yggdrasil.Distribution    (runDistT, uniform)
import           Yggdrasil.ExecutionModel  (Action (Create), run)
import           Yggdrasil.Functionalities (commonRandomString, randomOracle)
import           Yggdrasil.HList           (HList (Cons, Nil))

crsSameTest :: Action s Bool
crsSameTest = do
  (Cons crsHandle Nil) <-
    Create $ commonRandomString (uniform [0 .. 10000 :: Int])
  fst' <- crsHandle ()
  snd' <- crsHandle ()
  return (fst' == snd')

roSameTest :: Action s Bool
roSameTest = do
  (Cons (roHandle :: Int -> Action s Int) Nil) <-
    Create $ randomOracle (uniform [0 .. 1000 :: Int])
  fst' <- roHandle 1
  snd' <- roHandle 1
  return (fst' == snd')

roAllEqual :: Action s Bool
roAllEqual = do
  (Cons (roHandle :: Int -> Action s Int) Nil) <-
    Create $ randomOracle (uniform [0 .. 1000 :: Int])
  xs <- sequence [roHandle i | i <- [1 .. 1000]]
  return $ all (== head xs) (tail xs)

spec :: IO Spec
spec = do
  rnd <- getSystemDRG
  return $ do
    describe "common random string" $
      it "returns the same value" $
      (fst <$> runDistT (run crsSameTest) rnd) `shouldBe` Just True
    describe "random oracle" $ do
      it "returns the same for the same query" $
        (fst <$> runDistT (run roSameTest) rnd) `shouldBe` Just True
      it "is random with different queries" $
        (fst <$> runDistT (run roAllEqual) rnd) `shouldBe` Just False
