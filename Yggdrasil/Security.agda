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
open import Data.Rational using (ℚ)
open import Function using (_∘_)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Yggdrasil.List using (_∈_; here; there; with-proof; map≡-implies-∈≡)
open import Yggdrasil.World using (WorldType; WorldState; World; Oracle; Call; Strategy; Node; Action; weaken; call; call↓; _↑_; stnode; _∷_; []; ⌊exec⌋; _⊑_; Query; _∈↑_; abort; dist; _>>=_; call↯; query; path; _↑; strat; ⊤; tt; Gas; zero; suc; _⊓_)
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

data Action↯ {ℓ : Level} (σ : Set ℓ) (Γᵢ Γᵣ : WorldType ℓ)
    {hon-≡ : map weaken (hon Γᵢ) ≡ map weaken (hon Γᵣ)} : Gas → Set ℓ →
    Set (lsuc ℓ) where
  read  : Action↯ σ Γᵢ Γᵣ zero σ
  write : σ → Action↯ σ Γᵢ Γᵣ zero ⊤
  query : ∀ {Γ′ q} → q ∈ qry (node Γ′) → Γ′ ⊑ Γᵣ → (x : Query.A q) → Action↯ σ Γᵢ Γᵣ (Query.g q) (Query.B q x)
  abort : ∀ {A} → Action↯ σ Γᵢ Γᵣ zero A
  dist  : ∀ {A} → Dist A → Action↯ σ Γᵢ Γᵣ zero A
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γᵢ → (x : Call.A f) →
    Action↯ σ Γᵢ Γᵣ (Call.g f) (Call.B f x)
  _>>=_ : ∀ {A B g₁ g₂} → Action↯ σ Γᵢ Γᵣ {hon-≡} g₁ A →
    (A → Action↯ σ Γᵢ Γᵣ {hon-≡} g₂ B) →
    Action↯ σ Γᵢ Γᵣ (g₁ ⊓ g₂) B

record Simulator {ℓ : Level} (πᵢ πᵣ : World ℓ) : Set (lsuc ℓ) where
  Γᵢ : WorldType ℓ
  Γᵢ = World.Γ πᵢ
  Γᵣ : WorldType ℓ
  Γᵣ = World.Γ πᵣ
  field
    hon-≡ : map weaken (hon Γᵢ) ≡ map weaken (hon Γᵣ)
    state : Set ℓ
    initial : state
    call↯-map : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γᵣ → ∃[ g ]
      ((x : Call.A f) → Action↯ state Γᵢ Γᵣ {hon-≡} g (Call.B f x))
    query-map : ∀ {q} → q ∈↑ Γᵢ → ∃[ g ]
      ((x : Query.A q) → Action↯ state Γᵢ Γᵣ {hon-≡} g (Query.B q x))

open Simulator

Actionᵣ⇒Actionᵢ : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} {g : Gas} →
  (S : Simulator πᵢ πᵣ) → Oracle (World.Γ πᵣ) → state S →
  ∃[ g′ ] (Action (World.Γ πᵣ) g A → Action (World.Γ πᵢ) g′ (A × state S))
Action↯⇒Action : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} {g : Gas} →
  (S : Simulator πᵢ πᵣ) → Oracle (World.Γ πᵣ) → state S →
  ∃[ g′ ] (Action↯ (state S) (World.Γ πᵢ) (World.Γ πᵣ) {hon-≡ S} g A →
  Action (World.Γ πᵢ) g′ (A × state S))

private
  with-state : ∀ {ℓ Γ A Σ} → Σ → A → Action {ℓ} Γ zero (A × Σ)
  with-state σ x = dist (pure ⟨ x , σ ⟩)

  without-state : ∀ {ℓ Γ} {A Σ : Set ℓ} → (A × Σ) → Action {ℓ} Γ zero A
  without-state ⟨ x , _ ⟩ = dist (pure x)

Actionᵣ⇒Actionᵢ {g} S O σ = ?
--Actionᵣ⇒Actionᵢ S O σ ((call↓ {f} ∈Γᵣ x) ↑) with map≡-implies-∈≡ (sym (hon-≡ S)) ∈Γᵣ
--... | ⟨ _ , ⟨ ∈Γᵢ , refl ⟩ ⟩ = ⟨ ? ⊓ zero , call↓ ∈Γᵢ x ↑ >>= with-state σ ⟩
--Actionᵣ⇒Actionᵢ _ _ _ abort = ⟨ zero , abort ⟩
--Actionᵣ⇒Actionᵢ _ _ σ (dist D) = ⟨ zero ⊓ zero , dist D >>= with-state σ ⟩
--Actionᵣ⇒Actionᵢ S O σ (call↯ ∈Γ Γ⊑ x) = let
--    ⟨ g , α ⟩ = call↯-map S ∈Γ Γ⊑
--  in Action↯⇒Action S O σ (α x)
--Actionᵣ⇒Actionᵢ S O σ (α >>= β) = ? --⟨ ? , (Actionᵣ⇒Actionᵢ S O σ α) >>= (λ{
--    ⟨ x , σ′ ⟩ → Actionᵣ⇒Actionᵢ S O σ′ (β x)
--  }) ⟩

Action↯⇒Action = ?
--Action↯⇒Action S O σ read = dist (pure ⟨ σ , σ ⟩)
--Action↯⇒Action S O _ (write σ) = dist (pure ⟨ tt , σ ⟩)
--Action↯⇒Action S O σ (query ∈Γ Γ⊑ x) = Actionᵣ⇒Actionᵢ S O σ g (O (path Γ⊑ ∈Γ) x)
--Action↯⇒Action _ _ _ abort = ⟨ zero , abort ⟩
--Action↯⇒Action _ _ σ (dist D) = dist D >>= with-state σ
--Action↯⇒Action _ _ σ (call↯ ∈Γ Γ⊑ x) = call↯ ∈Γ Γ⊑ x >>= with-state σ
--Action↯⇒Action S O σ (α >>= β) = ? --(Action↯⇒Action S O σ (suc g) α) >>= λ{
--    ⟨ x , σ′ ⟩ → Action↯⇒Action S O σ′ g (β x)
--  }

extract-oracle : ∀ {ℓ πᵢ πᵣ} → Simulator {ℓ} πᵢ πᵣ → Oracle (World.Γ πᵣ) →
  Oracle (World.Γ πᵢ)
extract-oracle = ?
--extract-oracle S O g ∈Γ x = Action↯⇒Action S O (initial S) g (query-map S ∈Γ x)
--  >>= without-state

simulated-strategy : ∀ {ℓ πᵢ πᵣ A} → Simulator {ℓ} πᵢ πᵣ →
  Strategy (World.Γ πᵣ) A → Strategy (World.Γ πᵢ) A
simulated-strategy = ?
--simulated-strategy S str g = strat
--  (Actionᵣ⇒Actionᵢ S (oracle str) (initial S) g (init str) >>= without-state)
--  (extract-oracle S (oracle str) g)

record Adv[_,_]≤_ {ℓ : Level} (πᵢ πᵣ : World ℓ) (ε : ℚ) :
    Set (lsuc (lsuc ℓ)) where
  field
    simulator : Simulator πᵢ πᵣ
    proof :
      (str : Strategy (World.Γ πᵣ) Guess) →
      (⌊exec⌋ (simulated-strategy simulator str) (World.Σ πᵢ))
        ≈[ ε ]≈
      (⌊exec⌋ str (World.Σ πᵣ))

_≃_ : {ℓ : Level} → (πᵢ πᵣ : World ℓ) → Set (lsuc (lsuc ℓ))
πᵢ ≃ πᵣ = Adv[ πᵢ , πᵣ ]≤ 0

private
  +-≡0ˡ : ∀ {n m} → n + m ≡ 0 → n ≡ 0
  +-≡0ˡ {zero} _ = refl
  +-≡0ˡ {suc n} ()

  ^≢0 : ∀ {n m} → (suc n) ^ m ≢ 0
  ^≢0 {n} {zero} ()
  ^≢0 {n} {suc m} n^sm≡0 = ^≢0 {n} {m} (+-≡0ˡ n^sm≡0)

_≈_ : {ℓ : Level} → (πᵢ πᵣ : ℕ → World ℓ) → ℕ → Set (lsuc (lsuc ℓ))
_≈_ πᵢ πᵣ κ = Adv[ πᵢ κ , πᵣ κ ]≤ (_÷_ 1 (2 ^ κ) {fromWitnessFalse (^≢0 {1} {κ})})
