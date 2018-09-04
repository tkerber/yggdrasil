{-# LANGUAGE ScopedTypeVariables #-}

module ExecTests
  ( spec
  ) where

import           Crypto.Random            (getSystemDRG)
import           Data.Maybe               (fromJust)
import           Test.Hspec               (Spec, describe, it, shouldBe)
import           Test.Hspec.QuickCheck    (prop)
import           Yggdrasil.Distribution   (sample', uniform)
import           Yggdrasil.ExecutionModel (Action, Ref (External), doSample,
                                           run, self)

inSampleRange :: Int -> Bool
inSampleRange x = x > 4700 && x < 5300

sampleTest :: Action Int
sampleTest = sampleTest' 10000
  where
    sampleTest' :: Int -> Action Int
    sampleTest' 0 = return 0
    sampleTest' n = do
      x <- sampleTest' (n - 1)
      b <- doSample (uniform [0, 1])
      return $ x + b

spec :: IO Spec
spec = do
  rnd <- getSystemDRG
  let secparam = 128
  return $
    describe "action" $ do
      prop "obeys return" $ \(x :: String) ->
        sample' rnd (run secparam (return x)) == Just x
      it "is exteral" $
        sample' rnd (run secparam self) == Just External `shouldBe` True
      it "samples evenly" $
        inSampleRange (fromJust $ sample' rnd (run secparam sampleTest)) `shouldBe`
        True
