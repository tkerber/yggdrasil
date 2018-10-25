import Prelude.Cast

infixr 5 ^=

data (^=) : a -> b -> Type where
  Refl : x ^= x
  Extend : {a : Type} -> {b : Type} -> (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x ^= g x) -> f ^= g

eEqTransitive : a ^= b -> b ^= c -> a ^= c
eEqTransitive Refl eq = eq 
eEqTransitive eq Refl = eq 
eEqTransitive (Extend a _ prfab) (Extend _ d prfbc) = Extend a d (\x => eEqTransitive (prfab x) (prfbc x))

eEqSymmetric  : a ^= b -> b ^= a
eEqSymmetric Refl = Refl
eEqSymmetric (Extend a b prfab) = Extend b a (\x => eEqSymmetric (prfab x))

Cast (a = b) (a ^= b) where
  cast Refl = Refl

-- Tests

fiveEqFive : 5 ^= 5
fiveEqFive = Refl

Double1 : Nat -> Nat
Double1 x = x + x

Double2 : Nat -> Nat
Double2 x = 2 * x

doubleEqItems : (x : Nat) -> Double1 x ^= Double2 x
doubleEqItems n = rewrite plusZeroRightNeutral n in Refl

doubleEq : Double1 ^= Double2
doubleEq = Extend Double1 Double2 doubleEqItems
