module Yggdrasil.World where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; []; map)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level using (Level; Lift) renaming (suc to lsuc; lift to llift)
open import Yggdrasil.Probability using (Dist; pure; _>>=′_; lift)
open import Yggdrasil.List using (_∈_; here; there)

data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

data ⊥ {ℓ : Level} : Set ℓ where

T : ∀ {ℓ} → Bool → Set ℓ
T true = ⊤
T false = ⊥

record Query (ℓ : Level) : Set (lsuc ℓ) where
  constructor mkquery
  field
    A : Set ℓ
    B : A → Set ℓ

mknquery : {ℓ : Level} → Set ℓ → Set ℓ → Query ℓ
mknquery A B = mkquery A (λ _ → B)

record Node (ℓ : Level) : Set (lsuc ℓ)
record WorldType (ℓ : Level) : Set (lsuc ℓ)
data Action↑ {ℓ : Level} (N : Node ℓ) : Set ℓ → Set (lsuc ℓ)
data Action⊤ {ℓ : Level} (S : Set ℓ) (Γ : WorldType ℓ) : Set ℓ → Set (lsuc ℓ)

data WorldState {ℓ : Level} (Γ : WorldType ℓ) : Set (lsuc ℓ)
data WorldStates {ℓ : Level} : List (WorldType ℓ) → Set (lsuc ℓ)

record Node ℓ where
  inductive
  constructor mknode
  field
    state : Set ℓ
    chld  : List (WorldType ℓ)
    qry   : List (Query ℓ)

open Node


record Call (ℓ : Level) (N : Node ℓ) : Set (lsuc ℓ) where
  inductive
  constructor call
  field
    A : Set ℓ
    B : A → Set ℓ
    δ : (x : A) → Action↑ N (B x)

-- A non-dependently typed instance of call.
ncall : {ℓ : Level} {N : Node ℓ} → (A B : Set ℓ) → (A → Action↑ N B) → Call ℓ N
ncall A B δ = call A (λ _ → B) δ

weaken : ∀ {ℓ N} → Call ℓ N → Query ℓ
weaken c = record { A = Call.A c; B = Call.B c }

record WorldType ℓ where
  inductive
  constructor tynode
  field
    node : Node ℓ
    adv  : List (Call ℓ node)
    hon  : List (Call ℓ node)

open WorldType

data _⊑_ {ℓ : Level} : (Γ₁ Γ₂ : WorldType ℓ) → Set (lsuc ℓ) where
  here : ∀ {Γ} → Γ ⊑ Γ
  there : ∀ {Γ₁ Γ₂ Γ₃} → Γ₂ ∈ chld (node Γ₃) → Γ₁ ⊑ Γ₂ → Γ₁ ⊑ Γ₃

⊑-trans : ∀ {ℓ} {Γ₁ Γ₂ Γ₃ : WorldType ℓ} → Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
⊑-trans ⊑Γ here = ⊑Γ
⊑-trans ⊑Γ (there Γ′∈ ⊑Γ′) = there Γ′∈ (⊑-trans ⊑Γ ⊑Γ′)

⊑-right : ∀ {ℓ} {Γ₁ Γ₂ Γ₃ : WorldType ℓ} → Γ₂ ⊑ Γ₃ → Γ₁ ∈ chld (node Γ₂) → Γ₁ ⊑ Γ₃
⊑-right Γ⊑ ∈Γ = ⊑-trans (there ∈Γ here) Γ⊑

data Action⊤ {ℓ} S Γ where
  read  : Action⊤ S Γ S
  write : S → Action⊤ S Γ ⊤
  call↓ : ∀ {f} → f ∈ (hon Γ) → (x : Call.A f) → Action⊤ S Γ (Call.B f x)
  abort : ∀ {A} → Action⊤ S Γ A
  dist  : ∀ {A} → Dist A → Action⊤ S Γ A
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γ →
    (x : Call.A f) → Action⊤ S Γ (Call.B f x)
  _>>=_ : ∀ {A B} → Action⊤ S Γ A → (A → Action⊤ S Γ B) → Action⊤ S Γ B

data Action↑ {ℓ} N where
  read  : Action↑ N (state N)
  write : state N → Action↑ N ⊤
  call↓ : ∀ {Γ f} → f ∈ (hon Γ) → Γ ∈ chld N → (x : Call.A f) →
    Action↑ N (Call.B f x)
  abort : ∀ {A} → Action↑ N A
  dist  : ∀ {A} → Dist A → Action↑ N A
  query : ∀ {q} → q ∈ qry N → (x : Query.A q) → Action↑ N (Query.B q x)
  _>>=_ : ∀ {A B} → Action↑ N A → (A → Action↑ N B) → Action↑ N B

-- TODO: build full monad instances of all actions, and Dist -- once I figure
-- out how that works in agda.
return : ∀ {ℓ N A} → A → Action↑ {ℓ} N A
return x = dist (pure x)

infixl 1 _>>=_ _>>_

_>>_ : ∀ {ℓ N A B} → Action↑ {ℓ} N A → Action↑ {ℓ} N B → Action↑ {ℓ} N B
α >> β = α >>= (λ _ → β)

data WorldStates {ℓ} where
  [] : WorldStates []
  _∷_ : ∀ {Γ Γs} → WorldState Γ → WorldStates Γs → WorldStates (Γ ∷ Γs)

data WorldState {ℓ} Γ where
  stnode : state (node Γ) → WorldStates (chld (node Γ)) → WorldState Γ

record World (ℓ : Level) : Set (lsuc ℓ) where
  field
    Γ : WorldType ℓ
    Σ : WorldState Γ

data _∈↑_ {ℓ : Level} (q : Query ℓ) (Γ : WorldType ℓ) : Set (lsuc ℓ) where
  path : ∀ {Γ′} → Γ′ ⊑ Γ → q ∈ qry (node Γ′) → q ∈↑ Γ

Oracle : ∀ {ℓ} → Set ℓ → WorldType ℓ → Set (lsuc ℓ)
Oracle S Γ = ∀ {q} → q ∈↑ Γ → (x : Query.A q) → Action⊤ S Γ (Query.B q x)

record Strategy {ℓ : Level} (Γ : WorldType ℓ) (A : Set ℓ) {S : Set ℓ} : Set (lsuc ℓ) where
  constructor strat
  field
    state : S
    init : Action⊤ S Γ A
    oracle : Oracle S Γ



get : ∀ {ℓ Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → WorldState {ℓ} Γ₂ → state (node Γ₁)
get here (stnode Σ _) = Σ
get (there Γ′∈ ⊑Γ) (stnode _ Σs) = get ⊑Γ (lookup Γ′∈ Σs)
  where
    lookup : ∀ {Γ Γs} → Γ ∈ Γs → WorldStates Γs → WorldState Γ
    lookup here (Σ ∷ _) = Σ
    lookup (there Γ′∈) (_ ∷ Σs) = lookup Γ′∈ Σs

set : ∀ {ℓ Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → WorldState {ℓ} Γ₂ → state (node Γ₁) →
  WorldState {ℓ} Γ₂
set here (stnode Σ Σs) Σ′ = stnode Σ′ Σs
set (there Γ′∈ ⊑Γ) (stnode Σ Σs) Σ′ = stnode Σ (set′ Γ′∈ ⊑Γ Σs Σ′)
  where
    set′ : ∀ {Γ₁ Γ₂ Γs} → Γ₂ ∈ Γs → Γ₁ ⊑ Γ₂ → WorldStates Γs →
      state (node Γ₁) → WorldStates Γs
    set′ here ⊑Γ (Σ ∷ Σs) Σ′ = set ⊑Γ Σ Σ′ ∷ Σs
    set′ (there Γ∈) ⊑Γ (Σ ∷ Σs) Σ′ = Σ ∷ set′ Γ∈ ⊑Γ Σs Σ′

data Result {ℓ : Level} (A : Set ℓ) : Set ℓ where
  abort      : Result A
  out-of-gas : Result A
  result     : A → Result A

rmap : ∀ {ℓ A B} → (A → B) → Result {ℓ} A → Result {ℓ} B
rmap _ abort = abort
rmap _ out-of-gas = out-of-gas
rmap f (result x) = result (f x)

exec : ∀ {ℓ S Γ A} → Strategy {ℓ} Γ A {S} → WorldState {ℓ} Γ → ℕ →
  Dist (Result (Lift (lsuc ℓ) A))
exec⊤ : ∀ {ℓ S Γ A} → Oracle S Γ → Action⊤ S Γ A → S × WorldState {ℓ} Γ → ℕ →
  Dist (Result (A × (S × WorldState {ℓ} Γ)))
exec↑ : ∀ {ℓ S Γ₁ Γ₂ A} → Oracle S Γ₁ → Action↑ (node Γ₂) A →
  (S × WorldState {ℓ} Γ₁) → Γ₂ ⊑ Γ₁ → ℕ → Dist (Result (A × (S × WorldState {ℓ} Γ₁)))

-- NOTE: Gas is only used for termination here, it is NOT a computational model.
exec (strat S α O) Σ g = (exec⊤ O α ⟨ S , Σ ⟩ g) >>=′ (pure ∘ rmap (llift ∘ proj₁))

exec⊤ O read                    Σ g       = pure (result ⟨ proj₁ Σ , Σ ⟩)
exec⊤ O (write σ)               Σ g       = pure (result ⟨ tt , ⟨ σ , proj₂ Σ ⟩ ⟩)
exec⊤ O (call↓ {f = f} ∈Γ x)    Σ g       = exec↑ O (Call.δ f x) Σ here g
exec⊤ O abort                   Σ g       = pure abort
exec⊤ O (dist D)                Σ g       = lift D >>=′ λ{
  (llift x) → pure (result ⟨ x , Σ ⟩ ) }
exec⊤ O (call↯ {f = f} f∈ ⊑Γ x) Σ g       = exec↑ O (Call.δ f x) Σ ⊑Γ g
exec⊤ O (α >>= β)               Σ g       = (exec⊤ O α Σ g) >>=′ λ{
  (result ⟨ x , Σ′ ⟩) → exec⊤ O (β x) Σ′ g ;
  abort               → pure abort         ;
  out-of-gas          → pure out-of-gas    }

exec↑ O read                    Σ ⊑Γ g       = pure (result
  ⟨ get ⊑Γ (proj₂ Σ) , Σ ⟩)
exec↑ O (write σ)               Σ ⊑Γ g       = pure (result
  ⟨ tt , ⟨ proj₁ Σ , set ⊑Γ (proj₂ Σ) σ ⟩ ⟩)
exec↑ O abort                   Σ ⊑Γ g       = pure abort
exec↑ O (dist D)                Σ ⊑Γ g       = lift D >>=′
  λ{ (llift x) → pure (result ⟨ x , Σ ⟩) }
exec↑ O (query {q = q} q∈ x)    Σ ⊑Γ zero    = pure out-of-gas
exec↑ O (query {q = q} q∈ x)    Σ ⊑Γ (suc g) = exec⊤ O (O (path ⊑Γ q∈) x) Σ g
exec↑ O (call↓ {f = f} ∈Γ Γ∈ x) Σ ⊑Γ g       = exec↑ O (Call.δ f x) Σ (⊑-right ⊑Γ Γ∈) g
exec↑ O (α >>= β)               Σ ⊑Γ g       = (exec↑ O α Σ ⊑Γ g) >>=′ λ{
  (result ⟨ x , Σ′ ⟩) → exec↑ O (β x) Σ′ ⊑Γ g ;
  abort               → pure abort            ;
  out-of-gas          → pure out-of-gas       }
