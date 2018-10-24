{-# LANGUAGE ScopedTypeVariables #-}

module ExecTests
  ( spec
  ) where

import           Crypto.Random            (getSystemDRG)
import           Data.Maybe               (fromJust)
import           Test.Hspec               (Spec, describe, it, shouldBe)
import           Test.Hspec.QuickCheck    (prop)
import           Yggdrasil.Distribution   (sample', uniform)
import           Yggdrasil.ExecutionModel (Action (Sample), run)

inSampleRange :: Int -> Bool
inSampleRange x = x > 4700 && x < 5300

sampleTest :: Action s Int
sampleTest = sampleTest' 10000
  where
    sampleTest' :: Int -> Action s Int
    sampleTest' 0 = return 0
    sampleTest' n = do
      x <- sampleTest' (n - 1)
      b <- Sample (uniform [0, 1])
      return $ x + b

spec :: IO Spec
spec = do
  rnd <- getSystemDRG
  return $
    describe "action" $ do
      prop "obeys return" $ \(x :: String) ->
        sample' rnd (run (return x)) == Just x
      it "samples evenly" $
        inSampleRange (fromJust $ sample' rnd (run sampleTest)) `shouldBe` True
