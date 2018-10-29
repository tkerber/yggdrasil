module Yggdrasil.Distribution

import Control.Monad.Identity
import Data.Fin
import Data.QQ.SternBrocot
import Data.ZZ
import Yggdrasil.Extensible

interface Sampler s where
  sample : {n : Nat} -> s -> (Fin (S n), s)

data D : Type -> Type where
  ||| A value is a distribution.
  PureD : a -> D a
  ||| Sample from Fin, where n >= 2
  SampleD : {n : Nat} -> D (Fin (S (S n)))
  ||| Allow sampling depending on the value of a previous sample.
  BindD : D a -> (a -> D b) -> D b

Functor D where
  map f x = BindD x (PureD . f)

Applicative D where
  pure = PureD
  f <*> x = BindD f (\f' => BindD x (\x' => PureD (f' x')))

Monad D where
  (>>=) = BindD

allFin : (n : Nat) -> List (Fin n)
allFin Z = []
allFin (S n) = FZ :: map FS (allFin n)

Num QQ where
  a + b = ?add_qq
  a * b = ?mult_qq
  fromInteger i = ?fromInt_qq

Neg QQ where
  negate q = ?negate_qq
  a - b = ?subtract_qq

data Event : (a -> Bool) -> D a -> QQ -> Type where
  ||| If `f x` is true, it's pure distribution has probability 1.
  PureT : f a = True -> Event f (PureD a) (1 # 1)
  ||| If `f x` is false, it's pure distribution has probability 0.
  PureF : f a = False -> Event f (PureD a) (0 # 1)
  ||| If we know the number of samples where `f x` is true, 
  NFin : length (filter f (allFin (S (S n)))) = m ->
         Event f (SampleD {n=n}) (Pos m # S (S n))
  CondBind : (f x = True -> Event g (bnd x) p1) ->
             (f x = False -> Event g (bnd x) p2) ->
             Event f d p3 ->
             Event g (BindD d bnd) (p3 * p1 + (1 - p3) * p2)

data DualEvent : {d1 : D a} -> {d2 : D a} ->
                 (f : (a -> Bool)) ->
                 (p : QQ) ->
                 Event f d1 p ->
                 Event f d2 p ->
                 Type where
  MkDual : (f : a -> Bool) ->
           (p : QQ) ->
           (e1 : Event f d1 p) ->
           (e2 : Event f d2 p) ->
           DualEvent f p e1 e2

infixr 5 $=

data ($=) : D a -> D a -> Type where
  EEq : Eq a => ((x : a) -> DualEvent {d1=d1} {d2=d2} f p e1 e2) -> d1 $= d2
