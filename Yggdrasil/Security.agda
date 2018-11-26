module Yggdrasil.Security where

open import Data.List using (map)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax)
open import Level using (Level) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Yggdrasil.List using (_∈_)
open import Yggdrasil.World using (WorldType; World; Call; Strategy; weaken)
open WorldType

data Guess {ℓ : Level} : Set ℓ where
  real? ideal? : Guess

data Outcome : Set where
  ↯ ✔ : Outcome

record RouterConfig {ℓ : Level} : Set (lsuc ℓ) where
  field
    ref   : Guess {ℓ}
    real  : World ℓ
    ideal : World ℓ
    sim   : Σ[ σ ∈ Set ℓ ] (σ × (∀ {c} → σ → c ∈ adv (proj₁ ideal) →
      σ × (Σ (Call ℓ (node (proj₁ real))) (_∈ adv (proj₁ real)))))
    hon-≡ : map weaken (hon (proj₁ ideal)) ≡ map weaken (hon (proj₁ real))

open RouterConfig

router-world-type : ∀ {ℓ} → RouterConfig {ℓ} → WorldType ℓ
router-world-type = ?

router-world : ∀ {ℓ} → RouterConfig {ℓ} → Guess {ℓ} → World ℓ
router-world = ?

router-strategy : ∀ {ℓ A} → (rc : RouterConfig {ℓ}) →
  Strategy (proj₁ (ideal rc)) A → Strategy (router-world-type rc) A
router-strategy = ?

yggdrasil-game : ∀ {ℓ} → (rc : RouterConfig {ℓ}) →
  Strategy (proj₁ (ideal rc)) Guess → Guess {ℓ} → Outcome
yggdrasil-game = ?
