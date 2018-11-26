module Yggdrasil.World where

open import Data.List using (List; _∷_; []; map)
open import Data.Product using (_×_)
open import Level using (Level; suc)
open import Yggdrasil.List using (_∈_)

record WorldType (ℓ : Level) : Set (suc ℓ)
data Action {ℓ : Level} : (WorldType ℓ) → Set ℓ → Set (suc ℓ)

record Call (ℓ : Level) (Σ : Set ℓ) (Γ : List (WorldType ℓ)) : Set (suc ℓ) where
  field
    A : Set ℓ
    B : A → Set ℓ
    δ : Σ → (x : A) → Σ × B x

record WorldType ℓ where
  inductive
  field
    root : Set ℓ
    children : List (WorldType ℓ)
    adv  : List (Call ℓ root children)
    hon  : List (Call ℓ root children)

open WorldType

data Action {ℓ} where
  abort : ∀ {W A} → Action W A
  pure  : ∀ {W A} → A → Action W A
  call  : ∀ {W f} → f ∈ (hon W) → (x : Call.A f) → Action W (Call.B f x)

data WorldState {ℓ : Level} : WorldType ℓ → Set (suc ℓ)
data WorldStates {ℓ : Level} : List (WorldType ℓ) → Set (suc ℓ)

data WorldStates {ℓ} where
  [] : WorldStates []
  _∷_ : {W : WorldType ℓ} {Ws : List (WorldType ℓ)} → WorldState W →
    WorldStates Ws → WorldStates (W ∷ Ws)

data WorldState {ℓ} where
  node : {T : WorldType ℓ} → root T → WorldStates (children T) → WorldState T
