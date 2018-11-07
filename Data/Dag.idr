
module Data.Dag

%default total
%access public export

data Edge : Type -> Nat -> Type where
  MkEdge : {n : Nat} -> (a, b : Nat) -> {auto pa : LT a b} ->
           {auto pb : LT b n} -> c -> Edge c n

data Dag : Type -> Type -> Type where
  MkDag : (ns : List a) -> List (Edge b (length ns)) -> Dag a b


nodes : Dag a b -> Nat
nodes (MkDag ns es) = length ns

edges : (d : Dag a b) -> List (Edge b (nodes d))
edges (MkDag _ es) = es

data DagEdge : (d : Dag a b) -> Edge b (Dag.nodes d) -> Type where
  EZ : DagEdge (MkDag ns (e::es)) e
  ES : DagEdge (MkDag ns es) e' -> DagEdge (MkDag ns (e::es)) e'

startsAt : Edge a n -> Nat
startsAt (MkEdge a b c) = a

endsAt : Edge a n -> Nat
endsAt (MkEdge a b c) = b

data Path : (d : Dag a b) -> Nat -> Nat -> Type where
  Nil : {auto prf : LT n (nodes d)} -> Path d n n
  (::) : (e : Edge b (nodes d)) -> {auto isEdge : DagEdge d e} ->
         Path d n m -> {auto adjacent : Dag.endsAt e = n} ->
         Path d (Dag.startsAt e) m

minusLTE : LTE (minus a b) a
minusLTE {a=Z} = LTEZero
minusLTE {a} {b=Z} = rewrite minusZeroRight a in lteRefl
minusLTE {a=S a} {b=S b} = lteSuccRight minusLTE

minusGTIsLT : GT a b -> {auto sml1 : LTE a n} -> {auto sml2 : LTE b n} ->
              LT (n - a) (n - b)
minusGTIsLT {n=Z} {a=Z} {b=Z} gt impossible
minusGTIsLT {n=S n} {a=S a} {b=Z} _ = LTESucc (minusLTE {a=n} {b=a})
minusGTIsLT {n=S n} {a=S a} {b=S b} (LTESucc gt) {sml1=LTESucc sml1} {sml2=LTESucc sml2} =
  minusGTIsLT gt

reversePreservesLength : (l : List a) -> length l = length (reverse l)
reversePreservesLength = reverseOntoPreservesLength []
  where
    reverseOntoPreservesLength : (acc : List a) -> (l : List a) ->
                                 length acc + length l = length (reverseOnto acc l)
    reverseOntoPreservesLength acc [] = plusZeroRightNeutral (length acc)
    reverseOntoPreservesLength acc (x::xs) =
      rewrite sym (plusSuccRightSucc (length acc) (length xs)) in
      reverseOntoPreservesLength (x::acc) xs

||| Inverts paths in a dag. Each node at index n is mapped to index l - 1 - n.
invert : Dag a b -> Dag a b
invert (MkDag ns es) = MkDag (reverse ns)
  (rewrite sym (reversePreservesLength ns) in (map invertE es))
  where
    invertE : Edge c n -> Edge c n
    invertE (MkEdge {n=S n} a b {pa} {pb} c) =
      let sml1 : LTE b n = fromLteSucc pb
          sml2 : LTE a n = lteSuccLeft (lteTransitive pa sml1)
          pa' : LT (minus n b) (minus n a) = minusGTIsLT pa
          pb' : LT (minus n a) (S n) = LTESucc minusLTE
      in MkEdge (minus n b) (minus n a) c

retain : Dag a b -> List Nat -> Dag a b
retain d = retain' d . sort
  where
    retain' : Dag a b -> List Nat -> Dag a b
    retain' = ?retain

data DagView : Dag a b -> Dag a b -> Type where
  MkView : (d : Dag a b) ->
           (nlist : List Nat) ->
           DagView d (retain d nlist)

pred : (d : Dag a b) -> (n : Nat) -> {auto prf : LT n (nodes d)} ->
       (DPair (Dag a b) (\d' => DagView d d'))
pred d n = let l = filter (\m => isPred m n (edges d)) (count (nodes d))
  in MkDPair (retain d l) (MkView d l)
  where
    count : Nat -> List Nat
    count Z = []
    count (S n) = n :: count n
    isPred : {n : Nat} -> Nat -> Nat -> List (Edge c n) -> Bool
    isPred n m [] = False
    isPred n m (MkEdge a b _::es) = if n == a && m == b then True else isPred n m es
