module Yggdrasil.Zn

public export
data Zn : Nat -> Type where
  ZnZ : Zn (S n)
  ZnS : Zn n -> Zn (S n)

export
toBool : Zn 2 -> Bool
toBool ZnZ = False
toBool (ZnS ZnZ) = True

export
indexZn : (l : List a) -> Zn (length l) -> a
indexZn (x :: _) ZnZ = x
indexZn (_ :: xs) (ZnS n') = indexZn xs n'
