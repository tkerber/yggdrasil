{-# LANGUAGE ScopedTypeVariables #-}

module ExecTests (spec) where

import Crypto.Random
import Data.Maybe
import Test.Hspec
import Test.Hspec.QuickCheck
import Yggdrasil.ExecutionModel
import Yggdrasil.Distribution

inSampleRange :: Int -> Bool
inSampleRange x = x > 4700 && x < 5300

sampleTest :: Action Int
sampleTest = sampleTest' 10000
  where
    sampleTest' :: Int -> Action Int
    sampleTest' 0 = return 0
    sampleTest' n = do
        x <- sampleTest' (n-1)
        b <- doSample (uniform [0, 1])
        return $ x + b

spec :: IO Spec
spec = do
    rnd <- getSystemDRG
    return $ describe "action" $ do
        prop "obeys return" $ \(x::String) ->
            sample' rnd (run (return x)) == Just x
        it "is exteral" $
            sample' rnd (run self) == Just external `shouldBe` True
        it "samples evenly" $
            inSampleRange (fromJust $ sample' rnd (run sampleTest))
                `shouldBe` True
