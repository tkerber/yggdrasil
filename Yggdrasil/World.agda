module Yggdrasil.World where

open import Data.Bool using (Bool; T)
open import Data.List using (List; _∷_; []; map)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; suc)
open import Data.Product as Π using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String)
import Data.String.Unsafe as S
open import Function using (id)
open import Level using (Level; _⊔_; Lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

-- Auto-lifted variant of ⊤.
data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

Table : ∀ {ℓ} → Set ℓ → Set ℓ
Table A = List (String × A)

lookup : ∀ {ℓ A} → Table {ℓ} A → String → Maybe A
lookup [] _ = nothing
lookup (⟨ s₁ , x ⟩ ∷ xs) s₂ with s₁ S.≟ s₂
... | yes _ = just x
... | no _  = lookup xs s₂

module Weak where
  record WeakState {ℓ : Level} : Set (lsuc ℓ)

  record WeakTransition {ℓ : Level} : Set (lsuc ℓ) where
    inductive
    field
      A : Set ℓ
      B : A → Set ℓ
      Σ : A → WeakState {ℓ}

  record WeakState {ℓ} where
    inductive
    field
      δ↑ : Table (WeakTransition {ℓ})
      δ↓ : Table (WeakTransition {ℓ})

open Weak using (WeakState; WeakTransition)

record State {ℓ : Level} (Σʷ : WeakState {ℓ}) : Set (lsuc ℓ)
data Action {ℓ : Level} : {Σʷ₁ Σʷ₂ : WeakState {ℓ}} → (Σ₁ : Π.Σ (Set ℓ) id) →
    (Σ₂ : State Σʷ₂) → Set ℓ → Set (lsuc ℓ)

Transition↑ : {ℓ : Level} {Σʷ : WeakState {ℓ}} → (Σ₁ : Π.Σ (Set ℓ) id) →
  WeakTransition {ℓ} → Set (lsuc ℓ)
Transition↑ {Σʷ = Σʷ} Σ₁ T = (x : A T) → Π.Σ (State (Σ T x))
    (λ Σ₂ → Action {Σʷ₁ = Σʷ} Σ₁ Σ₂ (B T x))
  where open WeakTransition using (A; B; Σ)

Transition↓ : {ℓ : Level} → WeakTransition {ℓ} → Set (lsuc ℓ)
Transition↓ T = (x : A T) → State (Σ T x)
  where open WeakTransition using (A; Σ)

data Transitions↑ {ℓ : Level} (Σ : Π.Σ (Set ℓ) id) :
    Table (WeakTransition {ℓ}) → Set (lsuc ℓ) where
  [] : Transitions↑ Σ []
  _∷_ : ∀ {Σʷ T Ts name} → Transition↑ {Σʷ = Σʷ} Σ T → Transitions↑ Σ Ts →
    Transitions↑ Σ (⟨ name , T ⟩ ∷ Ts)

data Transitions↓ {ℓ : Level} :
    Table (WeakTransition {ℓ}) → Set (lsuc ℓ) where
  [] : Transitions↓ []
  _∷_ : ∀ {T Ts name} → Transition↓ T → Transitions↓ Ts →
    Transitions↓ (⟨ name , T ⟩ ∷ Ts)

record State {ℓ} Σʷ where
  inductive
  field
    Σ : Set ℓ
    σ : Σ
    δ↑ : Transitions↑ ⟨ Σ , σ ⟩ (WeakState.δ↑ Σʷ)
    δ↓ : Transitions↓ (WeakState.δ↓ Σʷ)

⌊_⌋ : ∀ {ℓ Σʷ} → (Σ : State {ℓ} Σʷ) → Π.Σ (Set ℓ) id
⌊ Σ ⌋ = ⟨ State.Σ Σ , State.σ Σ ⟩

lookup↓ : ∀ {ℓ xs δ} → δ ∈ xs → (Ts : Transitions↓ {ℓ} xs) → Transition↓ (proj₂ δ)
lookup↓ (here refl) (x ∷ _) = x
lookup↓ (there ∈xs) (_ ∷ xs) = lookup↓ ∈xs xs

∈↓ʷ⇒∈↓ : ∀ {ℓ Σʷ δ} {Σ : State Σʷ} → δ ∈ (WeakState.δ↓ Σʷ) →
  Transition↓ {ℓ} (proj₂ δ)
∈↓ʷ⇒∈↓ {Σ = Σ} δ∈ = lookup↓ δ∈ (State.δ↓ Σ)
--
--open Weak
--

data Action {ℓ} where
  get    : ∀ {Σʷ Σ} → Action {ℓ} {Σʷ} {Σʷ} ⌊ Σ ⌋ Σ (State.Σ Σ)
  set    : ∀ {Σʷ₁ Σʷ₂ Σ₁ Σ₂} → State.Σ Σ₂ → Action {ℓ} {Σʷ₁} {Σʷ₂} Σ₁ Σ₂ ⊤
  call   : ∀ {Σʷ δ} {Σ : State Σʷ} → (δ∈ : δ ∈ WeakState.δ↓ Σʷ) →
    (x : WeakTransition.A (proj₂ δ)) →
    Action {ℓ} {Σʷ} {WeakTransition.Σ (proj₂ δ) x} ⌊ Σ ⌋
      (∈↓ʷ⇒∈↓ {Σ = Σ} δ∈ x)
      (WeakTransition.B (proj₂ δ) x)
  return : ∀ {Σʷ Σ A} → Action {ℓ} {Σʷ} {Σʷ} ⌊ Σ ⌋ Σ A
  _>>=_  : ∀ {Σʷ₁ Σʷ₂ Σʷ₃ Σ₁ Σ₂ Σ₃ A B} →
    Action {ℓ} {Σʷ₁} {Σʷ₂} (⌊_⌋ {Σʷ = Σʷ₁} Σ₁) Σ₂ A →
    (A → Action {ℓ} {Σʷ₂} {Σʷ₃} ⌊ Σ₂ ⌋ Σ₃ B) →
    Action {ℓ} {Σʷ₁} {Σʷ₃} ⌊ Σ₁ ⌋ Σ₃ B

record ParallelComposable {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) {P : A → A → Set ℓ₂} :
    Set (ℓ₁ ⊔ ℓ₂) where
  field
    _||_ : A → A → A
    _∘_  : (x : A) → (y : A) → {_ : P x y} → A

data InterfaceMatches {ℓ : Level} : ℕ → (Σʷ₁ Σʷ₂ : WeakState {ℓ}) → Set (lsuc ℓ) where
  unreachable : ∀ {Σʷ₁ Σʷ₂} → InterfaceMatches 0 Σʷ₁ Σʷ₂
  match : ∀ {n Σʷ₁ Σʷ₂ δ₁} →
    -- For each interface in the outgoing to Σʷ₁
    δ₁ ∈ WeakState.δ↓ Σʷ₁ →
    Π.Σ (String × WeakTransition {ℓ}) (λ δ₂ →
      -- A corresponding interface exists in the incoming of Σʷ₂
      (δ₂ ∈ WeakState.δ↑ Σʷ₂) ×
      -- With the same name
      (proj₁ δ₁ ≡ proj₁ δ₂) ×
      -- The same input type
      Π.Σ (WeakTransition.A (proj₂ δ₁) ≡ WeakTransition.A (proj₂ δ₂)) (λ{
        refl → (x : WeakTransition.A (proj₂ δ₁)) →
          -- The same output type
          WeakTransition.B (proj₂ δ₁) x ≡ WeakTransition.B (proj₂ δ₂) x ×
          -- And preserving the fact that interfaces keep matching.
          InterfaceMatches n (WeakTransition.Σ (proj₂ δ₁) x)
            (WeakTransition.Σ (proj₂ δ₂) x)
    })) →
    InterfaceMatches (suc n) Σʷ₁ Σʷ₂

instance
  WeakStateParallelComposable : ∀ {ℓ : Level} → ParallelComposable {lsuc ℓ} (WeakState {ℓ}) {λ Σʷ₁ Σʷ₂ → ∀ n → InterfaceMatches n Σʷ₁ Σʷ₂}
  WeakStateParallelComposable = record
    { _||_ = ?
    ; _∘_  = λ Σʷ₁ Σʷ₂ → record
      { δ↑ = ?
      ; δ↓ = ?
      }
    }
--  ActionParallelComposable : ∀ {ℓ : Level} {Σʷ : WeakState {ℓ}} → (Σ : State Σʷ) → (A : Set ℓ) → ParallelComposable {ℓ} {P = InterfaceMatches
--ParallelComposable 

-- open import Data.Bool using (Bool; true; false)
-- open import Data.Empty using (⊥-elim)
-- open import Data.List using (List; _∷_; []; map)
-- open import Data.Maybe using (Maybe; nothing; just) renaming (map to mmap)
-- open import Data.Nat using (ℕ; zero; suc)
-- open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Function using (_∘_)
-- open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
-- open import Level using (Level; Lift) renaming (suc to lsuc; lift to llift)
-- open import Yggdrasil.Probability using (Dist; pure; _>>=′_; lift)
-- open import Yggdrasil.List using (_∈_; here; there)
-- 
-- data ⊤ {ℓ : Level} : Set ℓ where
--   tt : ⊤
-- 
-- data ⊥ {ℓ : Level} : Set ℓ where
-- 
-- T : ∀ {ℓ} → Bool → Set ℓ
-- T true = ⊤
-- T false = ⊥
-- 
-- record Query (ℓ : Level) : Set (lsuc ℓ) where
--   constructor mkquery
--   field
--     A : Set ℓ
--     B : A → Set ℓ
-- 
-- mknquery : {ℓ : Level} → Set ℓ → Set ℓ → Query ℓ
-- mknquery A B = mkquery A (λ _ → B)
-- 
-- record Node (ℓ : Level) : Set (lsuc ℓ)
-- record WorldType (ℓ : Level) : Set (lsuc ℓ)
-- data Action↑ {ℓ : Level} (N : Node ℓ) : Set ℓ → Set (lsuc ℓ)
-- data Action⊤ {ℓ : Level} (S : Set ℓ) (Γ : WorldType ℓ) : Set ℓ → Set (lsuc ℓ)
-- 
-- data WorldState {ℓ : Level} (Γ : WorldType ℓ) : Set (lsuc ℓ)
-- data WorldStates {ℓ : Level} : List (WorldType ℓ) → Set (lsuc ℓ)
-- 
-- record Node ℓ where
--   inductive
--   constructor mknode
--   field
--     state : Set ℓ
--     chld  : List (WorldType ℓ)
--     qry   : List (Query ℓ)
-- 
-- open Node
-- 
-- 
-- record Call (ℓ : Level) (N : Node ℓ) : Set (lsuc ℓ) where
--   inductive
--   constructor call
--   field
--     A : Set ℓ
--     B : A → Set ℓ
--     δ : (x : A) → Action↑ N (B x)
-- 
-- -- A non-dependently typed instance of call.
-- ncall : {ℓ : Level} {N : Node ℓ} → (A B : Set ℓ) → (A → Action↑ N B) → Call ℓ N
-- ncall A B δ = call A (λ _ → B) δ
-- 
-- weaken : ∀ {ℓ N} → Call ℓ N → Query ℓ
-- weaken c = record { A = Call.A c; B = Call.B c }
-- 
-- record WorldType ℓ where
--   inductive
--   constructor tynode
--   field
--     node : Node ℓ
--     adv  : List (Call ℓ node)
--     hon  : List (Call ℓ node)
-- 
-- open WorldType
-- 
-- data _⊑_ {ℓ : Level} : (Γ₁ Γ₂ : WorldType ℓ) → Set (lsuc ℓ) where
--   here : ∀ {Γ} → Γ ⊑ Γ
--   there : ∀ {Γ₁ Γ₂ Γ₃} → Γ₂ ∈ chld (node Γ₃) → Γ₁ ⊑ Γ₂ → Γ₁ ⊑ Γ₃
-- 
-- ⊑-trans : ∀ {ℓ} {Γ₁ Γ₂ Γ₃ : WorldType ℓ} → Γ₁ ⊑ Γ₂ → Γ₂ ⊑ Γ₃ → Γ₁ ⊑ Γ₃
-- ⊑-trans ⊑Γ here = ⊑Γ
-- ⊑-trans ⊑Γ (there Γ′∈ ⊑Γ′) = there Γ′∈ (⊑-trans ⊑Γ ⊑Γ′)
-- 
-- ⊑-right : ∀ {ℓ} {Γ₁ Γ₂ Γ₃ : WorldType ℓ} → Γ₂ ⊑ Γ₃ → Γ₁ ∈ chld (node Γ₂) → Γ₁ ⊑ Γ₃
-- ⊑-right Γ⊑ ∈Γ = ⊑-trans (there ∈Γ here) Γ⊑
-- 
-- data Action⊤ {ℓ} S Γ where
--   read  : Action⊤ S Γ S
--   write : S → Action⊤ S Γ ⊤
--   call↓ : ∀ {f} → f ∈ (hon Γ) → (x : Call.A f) → Action⊤ S Γ (Call.B f x)
--   abort : ∀ {A} → Action⊤ S Γ A
--   dist  : ∀ {A} → Dist A → Action⊤ S Γ A
--   call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γ →
--     (x : Call.A f) → Action⊤ S Γ (Call.B f x)
--   _>>=_ : ∀ {A B} → Action⊤ S Γ A → (A → Action⊤ S Γ B) → Action⊤ S Γ B
-- 
-- data Action↑ {ℓ} N where
--   read  : Action↑ N (state N)
--   write : state N → Action↑ N ⊤
--   call↓ : ∀ {Γ f} → f ∈ (hon Γ) → Γ ∈ chld N → (x : Call.A f) →
--     Action↑ N (Call.B f x)
--   abort : ∀ {A} → Action↑ N A
--   dist  : ∀ {A} → Dist A → Action↑ N A
--   query : ∀ {q} → q ∈ qry N → (x : Query.A q) → Action↑ N (Query.B q x)
--   _>>=_ : ∀ {A B} → Action↑ N A → (A → Action↑ N B) → Action↑ N B
-- 
-- -- TODO: build full monad instances of all actions, and Dist -- once I figure
-- -- out how that works in agda.
-- return : ∀ {ℓ N A} → A → Action↑ {ℓ} N A
-- return x = dist (pure x)
-- 
-- infixl 1 _>>=_ _>>_
-- 
-- _>>_ : ∀ {ℓ N A B} → Action↑ {ℓ} N A → Action↑ {ℓ} N B → Action↑ {ℓ} N B
-- α >> β = α >>= (λ _ → β)
-- 
-- data WorldStates {ℓ} where
--   [] : WorldStates []
--   _∷_ : ∀ {Γ Γs} → WorldState Γ → WorldStates Γs → WorldStates (Γ ∷ Γs)
-- 
-- data WorldState {ℓ} Γ where
--   stnode : state (node Γ) → WorldStates (chld (node Γ)) → WorldState Γ
-- 
-- record World (ℓ : Level) : Set (lsuc ℓ) where
--   field
--     Γ : WorldType ℓ
--     Σ : WorldState Γ
-- 
-- data _∈↑_ {ℓ : Level} (q : Query ℓ) (Γ : WorldType ℓ) : Set (lsuc ℓ) where
--   path : ∀ {Γ′} → Γ′ ⊑ Γ → q ∈ qry (node Γ′) → q ∈↑ Γ
-- 
-- Oracle : ∀ {ℓ} → Set ℓ → WorldType ℓ → Set (lsuc ℓ)
-- Oracle S Γ = ∀ {q} → q ∈↑ Γ → (x : Query.A q) → Action⊤ S Γ (Query.B q x)
-- 
-- record Strategy {ℓ : Level} (Γ : WorldType ℓ) (A : Set ℓ) {S : Set ℓ} : Set (lsuc ℓ) where
--   constructor strat
--   field
--     state : S
--     init : Action⊤ S Γ A
--     oracle : Oracle S Γ
-- 
-- 
-- 
-- get : ∀ {ℓ Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → WorldState {ℓ} Γ₂ → state (node Γ₁)
-- get here (stnode Σ _) = Σ
-- get (there Γ′∈ ⊑Γ) (stnode _ Σs) = get ⊑Γ (lookup Γ′∈ Σs)
--   where
--     lookup : ∀ {Γ Γs} → Γ ∈ Γs → WorldStates Γs → WorldState Γ
--     lookup here (Σ ∷ _) = Σ
--     lookup (there Γ′∈) (_ ∷ Σs) = lookup Γ′∈ Σs
-- 
-- set : ∀ {ℓ Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → WorldState {ℓ} Γ₂ → state (node Γ₁) →
--   WorldState {ℓ} Γ₂
-- set here (stnode Σ Σs) Σ′ = stnode Σ′ Σs
-- set (there Γ′∈ ⊑Γ) (stnode Σ Σs) Σ′ = stnode Σ (set′ Γ′∈ ⊑Γ Σs Σ′)
--   where
--     set′ : ∀ {Γ₁ Γ₂ Γs} → Γ₂ ∈ Γs → Γ₁ ⊑ Γ₂ → WorldStates Γs →
--       state (node Γ₁) → WorldStates Γs
--     set′ here ⊑Γ (Σ ∷ Σs) Σ′ = set ⊑Γ Σ Σ′ ∷ Σs
--     set′ (there Γ∈) ⊑Γ (Σ ∷ Σs) Σ′ = Σ ∷ set′ Γ∈ ⊑Γ Σs Σ′
-- 
-- data Result {ℓ : Level} (A : Set ℓ) : Set ℓ where
--   abort      : Result A
--   out-of-gas : Result A
--   result     : A → Result A
-- 
-- rmap : ∀ {ℓ A B} → (A → B) → Result {ℓ} A → Result {ℓ} B
-- rmap _ abort = abort
-- rmap _ out-of-gas = out-of-gas
-- rmap f (result x) = result (f x)
-- 
-- exec : ∀ {ℓ S Γ A} → Strategy {ℓ} Γ A {S} → WorldState {ℓ} Γ → ℕ →
--   Dist (Result (Lift (lsuc ℓ) A))
-- exec⊤ : ∀ {ℓ S Γ A} → Oracle S Γ → Action⊤ S Γ A → S × WorldState {ℓ} Γ → ℕ →
--   Dist (Result (A × (S × WorldState {ℓ} Γ)))
-- exec↑ : ∀ {ℓ S Γ₁ Γ₂ A} → Oracle S Γ₁ → Action↑ (node Γ₂) A →
--   (S × WorldState {ℓ} Γ₁) → Γ₂ ⊑ Γ₁ → ℕ → Dist (Result (A × (S × WorldState {ℓ} Γ₁)))
-- 
-- -- NOTE: Gas is only used for termination here, it is NOT a computational model.
-- exec (strat S α O) Σ g = (exec⊤ O α ⟨ S , Σ ⟩ g) >>=′ (pure ∘ rmap (llift ∘ proj₁))
-- 
-- exec⊤ O read                    Σ g       = pure (result ⟨ proj₁ Σ , Σ ⟩)
-- exec⊤ O (write σ)               Σ g       = pure (result ⟨ tt , ⟨ σ , proj₂ Σ ⟩ ⟩)
-- exec⊤ O (call↓ {f = f} ∈Γ x)    Σ g       = exec↑ O (Call.δ f x) Σ here g
-- exec⊤ O abort                   Σ g       = pure abort
-- exec⊤ O (dist D)                Σ g       = lift D >>=′ λ{
--   (llift x) → pure (result ⟨ x , Σ ⟩ ) }
-- exec⊤ O (call↯ {f = f} f∈ ⊑Γ x) Σ g       = exec↑ O (Call.δ f x) Σ ⊑Γ g
-- exec⊤ O (α >>= β)               Σ g       = (exec⊤ O α Σ g) >>=′ λ{
--   (result ⟨ x , Σ′ ⟩) → exec⊤ O (β x) Σ′ g ;
--   abort               → pure abort         ;
--   out-of-gas          → pure out-of-gas    }
-- 
-- exec↑ O read                    Σ ⊑Γ g       = pure (result
--   ⟨ get ⊑Γ (proj₂ Σ) , Σ ⟩)
-- exec↑ O (write σ)               Σ ⊑Γ g       = pure (result
--   ⟨ tt , ⟨ proj₁ Σ , set ⊑Γ (proj₂ Σ) σ ⟩ ⟩)
-- exec↑ O abort                   Σ ⊑Γ g       = pure abort
-- exec↑ O (dist D)                Σ ⊑Γ g       = lift D >>=′
--   λ{ (llift x) → pure (result ⟨ x , Σ ⟩) }
-- exec↑ O (query {q = q} q∈ x)    Σ ⊑Γ zero    = pure out-of-gas
-- exec↑ O (query {q = q} q∈ x)    Σ ⊑Γ (suc g) = exec⊤ O (O (path ⊑Γ q∈) x) Σ g
-- exec↑ O (call↓ {f = f} ∈Γ Γ∈ x) Σ ⊑Γ g       = exec↑ O (Call.δ f x) Σ (⊑-right ⊑Γ Γ∈) g
-- exec↑ O (α >>= β)               Σ ⊑Γ g       = (exec↑ O α Σ ⊑Γ g) >>=′ λ{
--   (result ⟨ x , Σ′ ⟩) → exec↑ O (β x) Σ′ ⊑Γ g ;
--   abort               → pure abort            ;
--   out-of-gas          → pure out-of-gas       }
