module Yggdrasil.ExecutionModel

--import Control.ST
import Yggdrasil.Distribution

data Action : Type -> Type -> Type where
  Abort : Action s a
  SecParam : Action s Nat
  Sample : D a -> Action s a
  -- Create : ??? (ST doesn't seem to do quite what we want...)
  Compose : Action s a -> (a -> Action s b) -> Action s b

mutual
  Functor (Action s) where
    map f x = Compose x (pure . f)

  Applicative (Action s) where
    pure = Sample . pure
    f <*> x = Compose f (\f' => map f' x)

Monad (Action s) where
  (>>=) = Compose
