{-# LANGUAGE ScopedTypeVariables #-}

module ExecTests (spec) where

import System.Random
import Test.Hspec
import Test.Hspec.QuickCheck
import Yggdrasil.ExecutionModel
import Yggdrasil.SimpleState

run' :: RandomGen g => g -> Action SimpleState b -> (Maybe b, g)
run' = run

spec :: Spec
spec = do
    describe "action" $ do
        prop "obeys return" $ \i (x::String) ->
            fst (run' (mkStdGen i) (return x)) == Just x
        prop "is exteral" $ \i ->
            fst (run' (mkStdGen i) self) == Just external
