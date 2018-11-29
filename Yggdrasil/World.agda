module Yggdrasil.World where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; []; map)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; ∃; ∃-syntax; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level using (Level; Lift) renaming (suc to lsuc; lift to llift)
open import Yggdrasil.Probability using (Dist; pure; _>>=_; lift)
open import Yggdrasil.List using (_∈_; here; there)

record Query (ℓ : Level) : Set (lsuc ℓ) where
  field
    A : Set ℓ
    B : A → Set ℓ

record Node (ℓ : Level) : Set (lsuc ℓ)
record WorldType (ℓ : Level) : Set (lsuc ℓ)
--data Action↯ {ℓ : Level} (Γ : WorldType ℓ) : Set ℓ → Set (lsuc ℓ)
data Action↑ {ℓ : Level} (N : Node ℓ) : Set ℓ → Set (lsuc ℓ)
data Action↓ {ℓ : Level} (Γ : WorldType ℓ) : Set ℓ → Set (lsuc ℓ)
data Action {ℓ : Level} (Γ : WorldType ℓ) : Set ℓ → Set (lsuc ℓ)

data WorldState {ℓ : Level} (Γ : WorldType ℓ) : Set (lsuc ℓ)
data WorldStates {ℓ : Level} : List (WorldType ℓ) → Set (lsuc ℓ)

record Node ℓ where
  inductive
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
    δ : (state N) → (x : A) → (state N) × Action↑ N (B x)

weaken : ∀ {ℓ N} → Call ℓ N → Query ℓ
weaken c = record { A = Call.A c; B = Call.B c }

record WorldType ℓ where
  inductive
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

data Action {ℓ} Γ where
  _↑ : ∀ {A} → Action↓ {ℓ} Γ A → Action {ℓ} Γ A
  abort : ∀ {A} → Action Γ A
  dist  : ∀ {A} → Dist A → Action Γ A
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γ → (x : Call.A f) →
    Action Γ (Call.B f x)
  _>>=_ : ∀ {A B} → Action Γ A → (A → Action Γ B) → Action Γ B

--A = Action↯ Γ A ⊎ Action↓ Γ A
--data Action↯ {ℓ} Γ where
--  abort : ∀ {A} → Action↯ Γ A
--  dist  : ∀ {A} → Dist A → Action↯ Γ A
--  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γ → (x : Call.A f) →
--    Action↯ Γ (Call.B f x)
--  _>>=_ : ∀ {A B} → Action↯ Γ A → (A → Action↯ Γ B) → Action↯ Γ B

data Action↓ {ℓ} Γ where
  call↓ : ∀ {f} → f ∈ (hon Γ) → (x : Call.A f) → Action↓ Γ (Call.B f x)

data Action↑ {ℓ} N where
  abort : ∀ {A} → Action↑ N A
  dist  : ∀ {A} → Dist A → Action↑ N A
  query : ∀ {q} → q ∈ qry N → (x : Query.A q) → Action↑ N (Query.B q x)
  _↑_   : ∀ {Γ A} → Action↓ Γ A → Γ ∈ chld N → Action↑ N A
  _>>=_ : ∀ {A B} → Action↑ N A → (A → Action↑ N B) → Action↑ N B

data WorldStates {ℓ} where
  [] : WorldStates []
  _∷_ : ∀ {Γ Γs} → WorldState Γ → WorldStates Γs → WorldStates (Γ ∷ Γs)

data WorldState {ℓ} Γ where
  stnode : state (node Γ) → WorldStates (chld (node Γ)) → WorldState Γ

World : (ℓ : Level) → Set (lsuc ℓ)
World ℓ = Σ (WorldType ℓ) WorldState

data _∈↑_ {ℓ : Level} (q : Query ℓ) (Γ : WorldType ℓ) : Set (lsuc ℓ) where
  path : ∀ {Γ′} → Γ′ ⊑ Γ → q ∈ qry (node Γ′) → q ∈↑ Γ

Oracle : ∀ {ℓ} → WorldType ℓ → Set (lsuc ℓ)
Oracle Γ = ∀ {q} → q ∈↑ Γ → (x : Query.A q) → Action Γ (Query.B q x)

record Strategy {ℓ : Level} (Γ : WorldType ℓ) (A : Set ℓ) : Set (lsuc ℓ) where
  constructor strat
  field
    init : Action Γ A
    oracle : Oracle Γ

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

⌊exec⌋ : ∀ {ℓ Γ A} → Strategy {ℓ} Γ A → WorldState {ℓ} Γ → ℕ →
  Dist (Maybe (Lift (lsuc ℓ) A))
exec : ∀ {ℓ Γ A} → Strategy {ℓ} Γ A → WorldState {ℓ} Γ → ℕ →
  Dist (Maybe (A × WorldState {ℓ} Γ))
exec′ : ∀ {ℓ Γ A} → Oracle Γ → Action Γ A → WorldState {ℓ} Γ → ℕ →
  Dist (Maybe (A × WorldState {ℓ} Γ))
--exec↯ : ∀ {ℓ Γ A} → Oracle Γ → Action↯ Γ A → WorldState {ℓ} Γ → ℕ →
--  Dist (Maybe (A × WorldState {ℓ} Γ))
exec↓ : ∀ {ℓ Γ₁ Γ₂ A} → Oracle Γ₁ → Action↓ Γ₂ A → WorldState {ℓ} Γ₁ →
  Γ₂ ⊑ Γ₁ → ℕ → Dist (Maybe (A × WorldState {ℓ} Γ₁))
exec↑ : ∀ {ℓ Γ₁ Γ₂ N A} → Oracle Γ₁ → Action↑ N A → WorldState {ℓ} Γ₁ →
  Γ₂ ⊑ Γ₁ → N ≡ node Γ₂ → ℕ → Dist (Maybe (A × WorldState {ℓ} Γ₁))

-- NOTE: Gas is only used for termination here, it is NOT a computational model.
⌊exec⌋ str Σ g = (exec str Σ g) >>= (pure ∘ mmap (llift ∘ proj₁))
exec (strat α O) Σ g = exec′ O α Σ g

exec′ _ _ _ zero = pure nothing
exec′ O (α ↑) Σ g = exec↓ O α Σ here g
exec′ _ abort _ _ = pure nothing
exec′ O (dist D) Σ (suc g) = lift D >>= λ{ (llift x) → pure (just ⟨ x , Σ ⟩ ) }
exec′ O (call↯ {f = f} f∈ ⊑Γ x) Σ (suc g) = let
    σ = get ⊑Γ Σ
    ⟨ σ′ , α ⟩ = Call.δ f σ x
    Σ′ = set ⊑Γ Σ σ′
  in exec↑ O α Σ′ ⊑Γ refl g
-- exec′ O (α ↯) Σ g = exec↯ O α Σ g
exec′ O (α >>= β) Σ (suc g) = (exec′ O α Σ (suc g)) >>= λ{
  (just ⟨ x , Σ′ ⟩) → exec′ O (β x) Σ′ g;
  nothing           → pure nothing }

-- exec↯ _ _ _ zero = pure nothing
-- exec↯ _ abort _ _ = pure nothing
-- exec↯ O (dist D) Σ (suc g) = lift D >>= λ{ (llift x) → pure (just ⟨ x , Σ ⟩ ) }
-- exec↯ O (call↯ {f = f} f∈ ⊑Γ x) Σ (suc g) = let
--     σ = get ⊑Γ Σ
--     ⟨ σ′ , α ⟩ = Call.δ f σ x
--     Σ′ = set ⊑Γ Σ σ′
--   in exec↑ O α Σ′ ⊑Γ refl g
-- exec↯ O (α >>= β) Σ (suc g) = (exec↯ O α Σ (suc g)) >>= λ{
--   (just ⟨ x , Σ′ ⟩) → exec↯ O (β x) Σ′ g;
--   nothing           → pure nothing }

exec↓ _ _ _ _ zero = pure nothing
exec↓ O (call↓ {f = f} f∈ x) Σ ⊑Γ (suc g) = let
    σ = get ⊑Γ Σ
    ⟨ σ′ , α ⟩ = Call.δ f σ x
    Σ′ = set ⊑Γ Σ σ′
  in exec↑ O α Σ′ ⊑Γ refl g

exec↑ _ _ _ _ _ zero = pure nothing
exec↑ O abort Σ ⊑Γ N≡ (suc g) = pure nothing
exec↑ O (dist D) Σ ⊑Γ N≡ (suc g) = lift D >>=
  λ{ (llift x) → pure (just ⟨ x , Σ ⟩) }
exec↑ O (query {q = q} q∈ x) Σ ⊑Γ refl (suc g) =
  exec′ O (O (path ⊑Γ q∈) x) Σ g
exec↑ O (α ↑ Γ′∈) Σ ⊑Γ refl (suc g) = exec↓ O α Σ (⊑-right ⊑Γ Γ′∈) g
exec↑ O (α >>= β) Σ ⊑Γ N≡ (suc g) = (exec↑ O α Σ ⊑Γ N≡ (suc g)) >>= λ{
  (just ⟨ x , Σ′ ⟩) → exec↑ O (β x) Σ′ ⊑Γ N≡ g;
  nothing           → pure nothing }