{-# LANGUAGE MultiParamTypeClasses #-}

module Yggdrasil.Distribution (Distribution(..)) where

import System.Random

class Distribution d b where
    sample :: RandomGen g => g -> d -> b
