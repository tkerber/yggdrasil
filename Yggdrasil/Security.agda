module Yggdrasil.Security where

open import Agda.Builtin.FromNat using (Number)
import Data.Nat.Literals as ℕLit
import Data.Rational.Literals as ℚLit
import Data.Integer.Literals as ℤLit
open import Data.List using (_∷_; []; map)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _≤_; _^_; _+_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe) renaming (map to mmap)
open import Data.Unit using (⊤; tt)
open import Data.Rational using (ℚ)
open import Function using (_∘_)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Yggdrasil.List using (_∈_; here; there; with-proof; map≡-implies-∈≡)
open import Yggdrasil.World using (WorldType; WorldState; World; Oracle; Call; Strategy; Node; Action; weaken; call; call↓; _↑_; stnode; _∷_; []; ⌊exec⌋; _⊑_; Query; _∈↑_; abort; dist; _>>=_; call↯; query; path; _↑; strat)
open import Yggdrasil.Probability using (Dist; _>>=_; pure; _≈[_]≈_)
open import Yggdrasil.Rational using (_÷_)
open WorldType
open Node
open Strategy

instance
  ℕnumber : Number ℕ
  ℕnumber = ℕLit.number
  ℤnumber : Number ℤ
  ℤnumber = ℤLit.number
  ℚnumber : Number ℚ
  ℚnumber = ℚLit.number

data Guess {ℓ : Level} : Set ℓ where
  real? ideal? : Guess

data Action↯ {ℓ : Level} (Γᵢ Γᵣ : WorldType ℓ)
    {hon-≡ : map weaken (hon Γᵢ) ≡ map weaken (hon Γᵣ)} : Set ℓ →
    Set (lsuc ℓ) where
  query : ∀ {Γ′ q} → q ∈ qry (node Γ′) → Γ′ ⊑ Γᵢ → (x : Query.A q) → Action↯ Γᵢ Γᵣ (Query.B q x)
  abort : ∀ {A} → Action↯ Γᵢ Γᵣ A
  dist  : ∀ {A} → Dist A → Action↯ Γᵢ Γᵣ A
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γᵣ → (x : Call.A f) →
    Action↯ Γᵢ Γᵣ (Call.B f x)
  _>>=_ : ∀ {A B} → Action↯ Γᵢ Γᵣ {hon-≡} A → (A → Action↯ Γᵢ Γᵣ {hon-≡} B) →
    Action↯ Γᵢ Γᵣ B

record Simulator {ℓ : Level} (Γᵢ Γᵣ : WorldType ℓ) : Set (lsuc ℓ) where
  field
    hon-≡ : map weaken (hon Γᵢ) ≡ map weaken (hon Γᵣ)
    state : Set ℓ
    initial : state
    call↯-map : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γᵢ →
      (x : Call.A f) → Action↯ Γᵢ Γᵣ {hon-≡} (Call.B f x)
    query-map : ∀ {q} → q ∈↑ Γᵣ → (x : Query.A q) → Action↯ Γᵢ Γᵣ {hon-≡} (Query.B q x)

open Simulator

Actionᵢ⇒Actionᵣ : ∀ {ℓ : Level} {Γᵢ Γᵣ : WorldType ℓ} {A : Set ℓ} →
  Simulator Γᵢ Γᵣ → Oracle Γᵢ → ℕ → Action Γᵢ A → Action Γᵣ A
Action↯⇒Action : ∀ {ℓ : Level} {Γᵢ Γᵣ : WorldType ℓ} {A : Set ℓ} →
  (S : Simulator Γᵢ Γᵣ) → Oracle Γᵢ → ℕ → Action↯ Γᵢ Γᵣ {hon-≡ S} A → Action Γᵣ A

Actionᵢ⇒Actionᵣ _ _ zero _ = abort
Actionᵢ⇒Actionᵣ S O (suc g) ((call↓ ∈Γᵢ x) ↑) with map≡-implies-∈≡ (hon-≡ S) ∈Γᵢ
... | ⟨ _ , ⟨ ∈Γᵣ , refl ⟩ ⟩ = call↓ ∈Γᵣ x ↑
Actionᵢ⇒Actionᵣ _ _ _ abort = abort
Actionᵢ⇒Actionᵣ _ _ _ (dist D) = dist D
Actionᵢ⇒Actionᵣ S O (suc g) (call↯ ∈Γ Γ⊑ x) = Action↯⇒Action S O g (call↯-map S ∈Γ Γ⊑ x)
Actionᵢ⇒Actionᵣ S O (suc g) (α >>= β) = (Actionᵢ⇒Actionᵣ S O (suc g) α) >>=
  (Actionᵢ⇒Actionᵣ S O g ∘ β)

Action↯⇒Action _ _ zero _ = abort
Action↯⇒Action S O (suc g) (query ∈Γ Γ⊑ x) = Actionᵢ⇒Actionᵣ S O g (O (path Γ⊑ ∈Γ) x)
Action↯⇒Action _ _ _ abort = abort
Action↯⇒Action _ _ _ (dist D) = dist D
Action↯⇒Action _ _ _ (call↯ ∈Γ Γ⊑ x) = call↯ ∈Γ Γ⊑ x
Action↯⇒Action S O (suc g) (α >>= β) = (Action↯⇒Action S O (suc g) α) >>=
  (Action↯⇒Action S O g ∘ β)

extract-oracle : ∀ {ℓ Γᵢ Γᵣ} → Simulator {ℓ} Γᵢ Γᵣ → Oracle Γᵢ → ℕ → Oracle Γᵣ
extract-oracle S O g ∈Γ x = Action↯⇒Action S O g (query-map S ∈Γ x)

simulated-strategy : ∀ {ℓ Γᵢ Γᵣ A} → Simulator {ℓ} Γᵢ Γᵣ → Strategy Γᵢ A → ℕ →
  Strategy Γᵣ A
simulated-strategy S str g = strat
  (Actionᵢ⇒Actionᵣ S (oracle str) g (init str))
  (extract-oracle S (oracle str) g)

record Challenge {ℓ : Level} : Set (lsuc ℓ) where
  field
    Γᵢ : WorldType ℓ
    Γᵣ : WorldType ℓ
    Σᵢ : WorldState Γᵢ
    Σᵣ : WorldState Γᵣ
    sim : Simulator Γᵢ Γᵣ

record Adv[_]≤_ {ℓ : Level} (c : Challenge {ℓ}) (ε : ℚ) :
    Set (lsuc (lsuc ℓ)) where
  field
    g-exec-min : ℕ
    g-sim-min : ℕ
    proof : (g-exec g-sim : ℕ) → g-exec-min ≤ g-exec → g-sim-min ≤ g-sim →
      (str : Strategy (Challenge.Γᵢ c) Guess) →
      (⌊exec⌋ str (Challenge.Σᵢ c) g-exec)
        ≈[ ε ]≈
      (⌊exec⌋ (simulated-strategy (Challenge.sim c) str g-sim) (Challenge.Σᵣ c)
        g-exec)

Perfect : {ℓ : Level} → Challenge {ℓ} → Set (lsuc (lsuc ℓ))
Perfect c = Adv[ c ]≤ 0

private
  +-≡0ˡ : ∀ {n m} → n + m ≡ 0 → n ≡ 0
  +-≡0ˡ {zero} _ = refl
  +-≡0ˡ {suc n} ()

  ^≢0 : ∀ {n m} → (suc n) ^ m ≢ 0
  ^≢0 {n} {zero} ()
  ^≢0 {n} {suc m} n^sm≡0 = ^≢0 {n} {m} (+-≡0ˡ n^sm≡0)

Computational : {ℓ : Level} → ℕ → (ℕ → Challenge {ℓ}) → Set (lsuc (lsuc ℓ))
Computational κ f = Adv[ f κ ]≤ (_÷_ 1 (2 ^ κ) {fromWitnessFalse (^≢0 {1} {κ})})
