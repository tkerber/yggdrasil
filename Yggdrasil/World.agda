module Yggdrasil.World where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; []; map)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level using (Level; Lift) renaming (suc to lsuc; lift to llift)
open import Yggdrasil.Probability using (Dist; pure; _>>=_; lift)
open import Yggdrasil.List using (_∈_; here; there)

data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

-- I don't like the current gas situation.
data Gas : Set where
  zero : Gas
  suc  : Gas → Gas
  _⊓_  : Gas → Gas → Gas

quite-a-bit′ : ℕ → Gas
quite-a-bit′ n = nest n (linear n)
  where
    linear : ℕ → Gas → Gas
    linear zero g = g
    linear (suc n) g = suc (linear n g)
    nest : ℕ → (Gas → Gas) → Gas
    nest zero g = g zero
    nest (suc n) g = g (nest n g ⊓ nest n g)

quite-a-bit : Gas
quite-a-bit = quite-a-bit′ 1000

record Query (ℓ : Level) : Set (lsuc ℓ) where
  constructor mkquery
  field
    A : Set ℓ
    B : A → Set ℓ
    g : Gas

mknquery : {ℓ : Level} → Set ℓ → Set ℓ → Gas → Query ℓ
mknquery A B g = mkquery A (λ _ → B) g

record Node (ℓ : Level) : Set (lsuc ℓ)
record WorldType (ℓ : Level) : Set (lsuc ℓ)
data _⊑_ {ℓ : Level} : (Γ₁ Γ₂ : WorldType ℓ) → Set (lsuc ℓ)
Oracle : ∀ {ℓ} → WorldType ℓ → Set (lsuc ℓ)
data Action↑ {ℓ : Level} {Γ′ : WorldType ℓ} (Γ : WorldType ℓ) (O : Oracle Γ′)
  (Γ⊑ : Γ ⊑ Γ′) : Gas → Set ℓ → Set (lsuc ℓ)
data Action↓ {ℓ : Level} {Γ′ : WorldType ℓ} (Γ : WorldType ℓ) (O : Oracle Γ′)
  (Γ⊑ : Γ ⊑ Γ′) : Gas → Set ℓ → Set (lsuc ℓ)
data Action {ℓ : Level} (Γ : WorldType ℓ) (O : Oracle Γ) : Gas → Set ℓ →
  Set (lsuc ℓ)

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
    g : Gas

-- A non-dependently typed instance of call.
--ncall : {ℓ : Level} {N : Node ℓ} → (A B : Set ℓ) → (g : Gas) → (A → Action↑ N g B) → Call ℓ N
--ncall A B g δ = call A (λ _ → B) g δ

weaken : ∀ {ℓ N} → Call ℓ N → Query ℓ
weaken c = record { A = Call.A c; B = Call.B c; g = Call.g c }

record WorldType ℓ where
  inductive
  constructor tynode
  field
    node : Node ℓ
    adv  : List (Call ℓ node)
    hon  : List (Call ℓ node)

open WorldType

data _⊑_ {ℓ} where
  here : ∀ {Γ} → Γ ⊑ Γ
  there : ∀ {Γ₁ Γ₂ Γ₃} → Γ₂ ∈ chld (node Γ₃) → Γ₁ ⊑ Γ₂ → Γ₁ ⊑ Γ₃

⊑-trans : ∀ {ℓ} {Γ₁ Γ₂ Γ₃ : WorldType ℓ} → Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
⊑-trans ⊑Γ here = ⊑Γ
⊑-trans ⊑Γ (there Γ′∈ ⊑Γ′) = there Γ′∈ (⊑-trans ⊑Γ ⊑Γ′)

⊑-right : ∀ {ℓ} {Γ₁ Γ₂ Γ₃ : WorldType ℓ} → Γ₂ ⊑ Γ₃ → Γ₁ ∈ chld (node Γ₂) → Γ₁ ⊑ Γ₃
⊑-right Γ⊑ ∈Γ = ⊑-trans (there ∈Γ here) Γ⊑

data Action {ℓ} Γ O where
  lift-suc : ∀ {A g} → Action Γ O g A → Action Γ O (suc g) A
  lift⊓₁ : ∀ {A g₁ g₂} → Action Γ O g₁ A → Action Γ O (g₁ ⊓ g₂) A
  lift⊓₂ : ∀ {A g₁ g₂} → Action Γ O g₂ A → Action Γ O (g₁ ⊓ g₂) A
  _↑ : ∀ {A g} → Action↓ {ℓ} Γ O here g A → Action {ℓ} Γ O (suc g) A
  abort : ∀ {A} → Action Γ O zero A
  dist  : ∀ {A} → Dist A → Action Γ O zero A
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γ →
    (x : Call.A f) → Action Γ O (suc (Call.g f)) (Call.B f x)
  _>>=_ : ∀ {A B g₁ g₂} → Action Γ O g₁ A → (A → Action Γ O g₂ B) → Action Γ O (g₁ ⊓ g₂) B

data Action↓ {ℓ} Γ O Γ⊑ where
  call↓ : ∀ {f} → f ∈ (hon Γ) → (x : Call.A f) → Action↓ Γ O Γ⊑ (suc (Call.g f)) (Call.B f x)

data Action↑ {ℓ} Γ O Γ⊑ where
  read  : Action↑ Γ O Γ⊑ zero (state (node Γ))
  write : state (node Γ) → Action↑ Γ O Γ⊑ zero ⊤
  abort : ∀ {A} → Action↑ Γ O Γ⊑ zero A
  dist  : ∀ {A} → Dist A → Action↑ Γ O Γ⊑ zero A
  query : ∀ {q} → q ∈ qry (node Γ) → (x : Query.A q) →
    Action↑ Γ O Γ⊑ (suc (Query.g q)) (Query.B q x)
  _↑_   : ∀ {Γ′ A g} → (∈Γ : Γ′ ∈ chld (node Γ)) →
    Action↓ Γ′ O (⊑-right Γ⊑ ∈Γ) g A →
    Action↑ Γ O Γ⊑ (suc g) A
  _>>=_ : ∀ {A B g₁ g₂} → Action↑ Γ O Γ⊑ g₁ A → (A → Action↑ Γ O Γ⊑ g₂ B) →
    Action↑ Γ O Γ⊑ (g₁ ⊓ g₂) B

-- TODO: build full monad instances of all actions, and Dist -- once I figure
-- out how that works in agda.
return : ∀ {ℓ Γ Γ′ O Γ⊑ A} → A → Action↑ {ℓ} {Γ′} Γ O Γ⊑ zero A
return x = dist (pure x)

infixl 1 _>>=_ _>>_

_>>_ : ∀ {ℓ Γ Γ′ O Γ⊑ A B g₁ g₂} → Action↑ {ℓ} Γ Γ′ O Γ⊑ g₁ A → Action↑ {ℓ} Γ O Γ⊑ g₂ B → Action↑ {ℓ} Γ O Γ⊑ (g₁ ⊓ g₂) B
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

OEmpty : ∀ {ℓ} {Γ : WorldType ℓ} → Oracle Γ
Oracle Γ = ∀ {q} → q ∈↑ Γ → (x : Query.A q) → Action Γ OEmpty (Query.g q) (Query.B q x)

OEmpty {q = q} _ _ = abort* (Query.g q)
  where
    abort* : ∀ {Γ A} g → Action Γ OEmpty g A
    abort* zero = abort
    abort* (suc g) = lift-suc (abort* g)
    abort* (g₁ ⊓ g₂) = lift⊓₁ (abort* g₁)

record Strategy {ℓ : Level} (Γ : WorldType ℓ) (A : Set ℓ) : Set (lsuc ℓ) where
  constructor strat
  field
    oracle : Oracle Γ
    init : ∃[ g ] Action Γ oracle g A

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

--⌊exec⌋ : ∀ {ℓ Γ A} → Strategy {ℓ} Γ A → WorldState {ℓ} Γ →
--  Dist (Maybe (Lift (lsuc ℓ) A))
--exec : ∀ {ℓ Γ A} → Strategy {ℓ} Γ A → WorldState {ℓ} Γ →
--  Dist (Maybe (A × WorldState {ℓ} Γ))
--exec′ : ∀ {ℓ Γ A} → Oracle Γ → (g : Gas) → Action Γ g A → WorldState {ℓ} Γ →
--  Dist (Maybe (A × WorldState {ℓ} Γ))
--exec↓ : ∀ {ℓ Γ₁ Γ₂ A} → Oracle Γ₁ → (g : Gas) → Action↓ Γ₂ g A → WorldState {ℓ} Γ₁ →
--  Γ₂ ⊑ Γ₁ → Dist (Maybe (A × WorldState {ℓ} Γ₁))
--exec↑ : ∀ {ℓ Γ₁ Γ₂ A} → Oracle Γ₁ → (g : Gas) → Action↑ (node Γ₂) g A → WorldState {ℓ} Γ₁ →
--  Γ₂ ⊑ Γ₁ → Dist (Maybe (A × WorldState {ℓ} Γ₁))
--
---- NOTE: Gas is only used for termination here, it is NOT a computational model.
--⌊exec⌋ str Σ = (exec str Σ) >>= (pure ∘ mmap (llift ∘ proj₁))
--exec (strat ⟨ g , α ⟩ O) Σ = exec′ O g α Σ
--
--exec′ O (suc g)   (α ↑)                   Σ = exec↓ O g α Σ here
--exec′ O zero      abort                   Σ = pure nothing
--exec′ O zero      (dist D)                Σ = lift D >>= λ{ (llift x) → pure (just ⟨ x , Σ ⟩ ) }
--exec′ O (suc g)   (call↯ {f = f} f∈ ⊑Γ x) Σ = exec↑ O g (Call.δ f x) Σ ⊑Γ
--exec′ O (g₁ ⊓ g₂) (α >>= β)               Σ = (exec′ O g₁ α Σ) >>= λ{
--  (just ⟨ x , Σ′ ⟩) → exec′ O g₂ (β x) Σ′;
--  nothing           → pure nothing }
--
--exec↓ O (suc g) (call↓ {f = f} f∈ x) Σ ⊑Γ = exec↑ O g (Call.δ f x) Σ ⊑Γ
--
---- _>>=_ : ∀ {A B g₁ g₂} → Action↑ N g₁ A → (A → Action↑ N g₂ B) → Action↑ N (suc (g₁ + g₂)) B
--exec↑ O zero      read                 Σ ⊑Γ = pure (just ⟨ get ⊑Γ Σ , Σ ⟩)
--exec↑ O zero      (write σ)            Σ ⊑Γ = pure (just ⟨ tt , set ⊑Γ Σ σ ⟩)
--exec↑ O zero      abort                Σ ⊑Γ = pure nothing
--exec↑ O zero      (dist D)             Σ ⊑Γ = lift D >>=
--  λ{ (llift x) → pure (just ⟨ x , Σ ⟩) }
--exec↑ O (suc g)   (query {q = q} q∈ x) Σ ⊑Γ = exec′ O g (O (path ⊑Γ q∈) x) Σ
--exec↑ O (suc g)   (α ↑ Γ′∈)            Σ ⊑Γ = exec↓ O g α Σ (⊑-right ⊑Γ Γ′∈)
--exec↑ O (g₁ ⊓ g₂) (α >>= β)            Σ ⊑Γ = (exec↑ O g₁ α Σ ⊑Γ)
--  >>= λ{
--    (just ⟨ x , Σ′ ⟩) → exec↑ O g₂ (β x) Σ′ ⊑Γ;
--    nothing           → pure nothing }
