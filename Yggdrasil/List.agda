module Yggdrasil.List where

open import Data.List using (List; _∷_)
open import Level using (Level)

data _∈_ {ℓ : Level} {A : Set ℓ} : A → List A → Set ℓ where
  here : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  there : {x y : A} {xs : List A} → y ∈ xs → y ∈ (x ∷ xs)
