module Yggdrasil.World where

open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; []; map)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Level using (Level; suc)
open import Yggdrasil.List using (_∈_)

record Query (ℓ : Level) : Set (suc ℓ) where
  field
    A : Set ℓ
    B : A → Set ℓ

record WorldType (ℓ : Level) : Set (suc ℓ)
data Action↯ {ℓ : Level} (Γ : WorldType ℓ) : Set ℓ → Set (suc ℓ)
data Action↑ {ℓ : Level} (Γs : List (WorldType ℓ)) (Qs : List (Query ℓ)) : Set ℓ → Set (suc ℓ)
data Action↓ {ℓ : Level} (Γ : WorldType ℓ) : Set ℓ → Set (suc ℓ)
Action : {ℓ : Level} → WorldType ℓ → Set ℓ → Set (suc ℓ)
Action Γ A = Action↯ Γ A ⊎ Action↓ Γ A

data WorldState {ℓ : Level} (Γ : WorldType ℓ) : Set (suc ℓ)
data WorldStates {ℓ : Level} : List (WorldType ℓ) → Set (suc ℓ)


record Call (ℓ : Level) (Σ : Set ℓ) (Γs : List (WorldType ℓ))
    (Qs : List (Query ℓ)) : Set (suc ℓ) where
  inductive
  field
    A : Set ℓ
    B : A → Set ℓ
    δ : Σ → (x : A) → Σ × Action↑ Γs Qs (B x)

record WorldType ℓ where
  inductive
  field
    root : Set ℓ
    chld : List (WorldType ℓ)
    qry  : List (Query ℓ)
    adv  : List (Call ℓ root chld qry)
    hon  : List (Call ℓ root chld qry)

open WorldType

data Action↯ {ℓ} Γ where
  call↯ : ∀ {f} → f ∈ (adv Γ) → (x : Call.A f) → Action↯ Γ (Call.B f x)
  lift↯ : ∀ {Γ′ A} → Action↯ Γ′ A → Γ′ ∈ (chld Γ) → Action↯ Γ A

data Action↓ {ℓ} Γ where
  call↓ : ∀ {f} → f ∈ (hon Γ) → (x : Call.A f) → Action↓ Γ (Call.B f x)

data Action↑ {ℓ} Γs Qs where
  abort : ∀ {A} → Action↑ Γs Qs A
  pure  : ∀ {A} → A → Action↑ Γs Qs A
  query : ∀ {q} → q ∈ Qs → (x : Query.A q) → Action↑ Γs Qs (Query.B q x)
  _↑    : ∀ {Γ A} → Action↓ Γ A → Γ ∈ Γs → Action↑ Γs Qs A
  _>>=_ : ∀ {A B} → Action↑ Γs Qs A → (A → Action↑ Γs Qs B) → Action↑ Γs Qs B

data WorldStates {ℓ} where
  [] : WorldStates []
  _∷_ : ∀ {Γ Γs} → WorldState Γ → WorldStates Γs → WorldStates (Γ ∷ Γs)

data WorldState {ℓ} Γ where
  node : root Γ → WorldStates (chld Γ) → WorldState Γ

data _∈↑_ {ℓ : Level} (q : Query ℓ) (Γ : WorldType ℓ) : Set (suc ℓ) where
  here : q ∈ qry Γ → q ∈↑ Γ
  there : ∀ {Γ′} → q ∈↑ Γ′ → Γ′ ∈ chld Γ → q ∈↑ Γ

record Strategy {ℓ : Level} (Γ : WorldType ℓ) (A : Set ℓ) : Set (suc ℓ) where
  constructor strat
  field
    init : Action Γ A
    oracle : ∀ {q} → q ∈↑ Γ → (x : Query.A q) → Action Γ (Query.B q x)

exec : ∀ {ℓ Γ A} → Strategy {ℓ} Γ A → WorldState {ℓ} Γ → Maybe A
exec = ?
