module Yggdrasil.Distribution

import Control.Monad.Identity
import Data.Fin
import Data.QQ.SternBrocot
import Data.ZZ
import Yggdrasil.Extensible

%access public export
%default total

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

nzMultNzIsNz : {n : Nat} -> {m : Nat} -> LTE 1 n -> LTE 1 m -> LTE 1 (n * m)
nzMultNzIsNz {n=Z} _ _ impossible
nzMultNzIsNz {m=Z} _ _ impossible
nzMultNzIsNz {n=S n} {m=S m} _ _ = LTESucc LTEZero

nomDenomAdd : QPlus -> QPlus -> (ZZ, ZZ, Subset Nat (\x => GT x 0))
nomDenomAdd q1 q2 = let
    (n1, d1) = extractQPlus q1;
    (n2, d2) = extractQPlus q2;
    a' = getWitness n1 * getWitness d2;
    b' = getWitness n2 * getWitness d1 in
    (Pos a', Pos b', Element (getWitness d1 * getWitness d2) (nzMultNzIsNz (getProof d1) (getProof d2)))

qplusMult : QPlus -> QPlus -> QPlus
qplusMult q1 q2 = let
    (n1, d1) = extractQPlus q1;
    (n2, d2) = extractQPlus q2;
    n = getWitness n1 * getWitness n2;
    d = getWitness d1 * getWitness d2 in
    injectQPlus n d
      (nzMultNzIsNz (getProof n1) (getProof n2))
      (nzMultNzIsNz (getProof d1) (getProof d2))


mutual
  Num QQ where
    Zero + b = b
    b + Zero = b
    (Neg a) + (Neg b) = let (a, b, c) = nomDenomAdd a b in
      (#) (negate (b + a)) (getWitness c) {dGtZ=getProof c}
    (Neg a) + (Pos b) = let (a, b, c) = nomDenomAdd a b in
      (#) (b - a) (getWitness c) {dGtZ=getProof c}
    (Pos a) + (Pos b) = let (a, b, c) = nomDenomAdd a b in
      (#) (a + b) (getWitness c) {dGtZ=getProof c}
    (Pos a) + (Neg b) = let (a, b, c) = nomDenomAdd a b in
      (#) (a - b) (getWitness c) {dGtZ=getProof c}
    Zero * _ = Zero
    _ * Zero = Zero
    (Neg a) * (Neg b) = Pos (qplusMult a b)
    (Neg a) * (Pos b) = Neg (qplusMult a b)
    (Pos a) * (Neg b) = Neg (qplusMult a b)
    (Pos a) * (Pos b) = Pos (qplusMult a b)
    fromInteger i = fromInteger i # 1

  Neg QQ where
    negate Zero = Zero
    negate (Pos q) = (Neg q)
    negate (Neg q) = (Pos q)
    a - b = a + (negate b)

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
