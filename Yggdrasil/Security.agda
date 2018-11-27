module Yggdrasil.Security where

open import Data.List using (_∷_; []; map)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe) renaming (map to mmap)
open import Data.Unit using (⊤; tt)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Yggdrasil.List using (_∈_; here; there; with-proof; map≡-implies-∈≡)
open import Yggdrasil.World using (WorldType; WorldState; World; Call; Strategy; Node; Action↑; weaken; call; call↓; _↑_; stnode; _∷_; []; exec)
open WorldType
open Node

data Guess {ℓ : Level} : Set ℓ where
  real? ideal? : Guess

data Outcome : Set where
  ↯ ✔ : Outcome

record RouterConfig {ℓ : Level} : Set (lsuc ℓ) where
  field
    real  : World ℓ
    ideal : World ℓ
    sim   : Σ[ σ ∈ Set ℓ ] (σ × (∀ {c} → σ → c ∈ adv (proj₁ ideal) →
      σ × (Σ (Call ℓ (node (proj₁ real))) (_∈ adv (proj₁ real)))))
    hon-≡ : map weaken (hon (proj₁ ideal)) ≡ map weaken (hon (proj₁ real))

open RouterConfig

router-world-type : ∀ {ℓ} → RouterConfig {ℓ} → WorldType ℓ
router-world-type {ℓ} rc = record
  { node = router-node
  ; adv = []
  ; hon = map (λ{c → call (Call.A (proj₁ c)) (Call.B (proj₁ c)) (hon-map′ c)})
    (with-proof (hon (proj₁ (ideal rc))))
  }
  where
    router-node : Node ℓ
    router-node = record
      { state = Σ (Guess {ℓ}) (λ{ ideal? → Lift ℓ ⊤ ; real? → proj₁ (sim rc)})
      ; chld  = proj₁ (ideal rc) ∷ proj₁ (real rc) ∷ []
      ; qry   = []
      } 
    hon-map′ : (c : Σ (Call ℓ (node (proj₁ (ideal rc)))) (_∈ (hon (proj₁ (ideal rc))))) →
      state router-node → (x : Call.A (proj₁ c)) →
      (state router-node) × Action↑ router-node (Call.B (proj₁ c) x)
    hon-map′ ⟨ call A B δ , ∈ideal ⟩ ⟨ ideal? , lift tt ⟩ x
      = ⟨ ⟨ ideal? , lift tt ⟩ , call↓ ∈ideal x ↑ here ⟩
    hon-map′ ⟨ call A B δ , ∈ideal ⟩ ⟨ real? , σ ⟩ x with map≡-implies-∈≡ (hon-≡ rc) ∈ideal
    ... | ⟨ _ , ⟨ ∈real , refl ⟩ ⟩ = ⟨ ⟨ real? , σ ⟩ , call↓ ∈real x ↑ there here ⟩

router-world-state : ∀ {ℓ} → (rc : RouterConfig {ℓ}) → Guess {ℓ} →
  WorldState (router-world-type rc)
router-world-state rc real? = stnode ⟨ real? , proj₁ (proj₂ (sim rc)) ⟩
  (proj₂ (ideal rc) ∷ proj₂ (real rc) ∷ [])
router-world-state rc ideal? = stnode ⟨ ideal? , lift tt ⟩
  (proj₂ (ideal rc) ∷ proj₂ (real rc) ∷ [])

router-strategy : ∀ {ℓ A} → (rc : RouterConfig {ℓ}) →
  Strategy (proj₁ (ideal rc)) A → Strategy (router-world-type rc) A
router-strategy = ?

yggdrasil-game : ∀ {ℓ} → (rc : RouterConfig {ℓ}) →
  Strategy (proj₁ (ideal rc)) Guess → Guess {ℓ} → ℕ → Maybe (Guess {ℓ})
yggdrasil-game rc str world gas = mmap proj₁ (exec (router-strategy rc str)
  (router-world-state rc world) gas)
