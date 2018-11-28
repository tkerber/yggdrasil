module Yggdrasil.Security where

open import Data.List using (_∷_; []; map)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe) renaming (map to mmap)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Yggdrasil.List using (_∈_; here; there; with-proof; map≡-implies-∈≡)
open import Yggdrasil.World using (WorldType; WorldState; World; Oracle; Call; Strategy; Node; Action; weaken; call; call↓; _↑_; stnode; _∷_; []; exec; _⊑_; Query; _∈↑_; abort; dist; _>>=_; call↯; query; path; _↑)
open import Yggdrasil.Probability using (Dist; _>>=_; pure)
open WorldType
open Node

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
  Simulator Γᵢ Γᵣ → Oracle Γᵢ → Action Γᵢ A → Action Γᵣ A
Action↯⇒Action : ∀ {ℓ : Level} {Γᵢ Γᵣ : WorldType ℓ} {A : Set ℓ} →
  (S : Simulator Γᵢ Γᵣ) → Oracle Γᵢ → Action↯ Γᵢ Γᵣ {hon-≡ S} A → Action Γᵣ A

Actionᵢ⇒Actionᵣ S O ((call↓ ∈Γᵢ x) ↑) with map≡-implies-∈≡ (hon-≡ S) ∈Γᵢ
... | ⟨ _ , ⟨ ∈Γᵣ , refl ⟩ ⟩ = call↓ ∈Γᵣ x ↑
Actionᵢ⇒Actionᵣ _ _ abort = abort
Actionᵢ⇒Actionᵣ _ _ (dist D) = dist D
Actionᵢ⇒Actionᵣ S O (call↯ ∈Γ Γ⊑ x) = Action↯⇒Action S O (call↯-map S ∈Γ Γ⊑ x)
Actionᵢ⇒Actionᵣ S O (α >>= β) = (Actionᵢ⇒Actionᵣ S O α) >>=
  (Actionᵢ⇒Actionᵣ S O ∘ β)

-- FIXME: The termination checker (understandably) doesn't like this. Can we
-- delay the recursion to runtime?
Action↯⇒Action S O (query ∈Γ Γ⊑ x) = {!Actionᵢ⇒Actionᵣ S O (O (path Γ⊑ ∈Γ) x)!}
Action↯⇒Action _ _ abort = abort
Action↯⇒Action _ _ (dist D) = dist D
Action↯⇒Action _ _ (call↯ ∈Γ Γ⊑ x) = call↯ ∈Γ Γ⊑ x
Action↯⇒Action S O (α >>= β) = (Action↯⇒Action S O α) >>=
  (Action↯⇒Action S O ∘ β)


record Challenge {ℓ : Level} : Set (lsuc ℓ) where
  field
    Γᵣ : WorldType ℓ
    Γᵢ : WorldType ℓ
    Σᵣ : WorldState Γᵣ
    Σᵢ : WorldState Γᵢ
    sim : Simulator Γᵢ Γᵣ
    --sim   : Σ[ σ ∈ Set ℓ ] (σ × (∀ {c} → σ → c ∈ adv (proj₁ ideal) →
    --  σ × (Σ (Call ℓ (node (proj₁ real))) (_∈ adv (proj₁ real)))))
 -- strategy : 

--exec-ideal : {ℓ : Level} → (c : Challenge {ℓ}) → (s : Strategy (proj₁ (ideal c)))

--private
--  relevel : {ℓ₁ ℓ₂ : Level} → Guess {ℓ₁} → Guess {ℓ₂}
--  relevel real? = real?
--  relevel ideal? = ideal?
--
--data Outcome : Set where
--  ↯ ✔ : Outcome
--
--record RouterConfig {ℓ : Level} : Set (lsuc ℓ) where
--  field
--    real  : World ℓ
--    ideal : World ℓ
--    sim   : Σ[ σ ∈ Set ℓ ] (σ × (∀ {c} → σ → c ∈ adv (proj₁ ideal) →
--      σ × (Σ (Call ℓ (node (proj₁ real))) (_∈ adv (proj₁ real)))))
--    hon-≡ : map weaken (hon (proj₁ ideal)) ≡ map weaken (hon (proj₁ real))
--
--open RouterConfig
--
--router-world-type : ∀ {ℓ} → RouterConfig {ℓ} → WorldType ℓ
--router-world-type {ℓ} rc = record
--  { node = router-node
--  ; adv = []
--  ; hon = map (λ{c → call (Call.A (proj₁ c)) (Call.B (proj₁ c)) (hon-map′ c)})
--    (with-proof (hon (proj₁ (ideal rc))))
--  }
--  where
--    router-node : Node ℓ
--    router-node = record
--      { state = Σ (Guess {ℓ}) (λ{ ideal? → Lift ℓ ⊤ ; real? → proj₁ (sim rc)})
--      ; chld  = proj₁ (ideal rc) ∷ proj₁ (real rc) ∷ []
--      ; qry   = []
--      } 
--    hon-map′ : (c : Σ (Call ℓ (node (proj₁ (ideal rc)))) (_∈ (hon (proj₁ (ideal rc))))) →
--      state router-node → (x : Call.A (proj₁ c)) →
--      (state router-node) × Action↑ router-node (Call.B (proj₁ c) x)
--    hon-map′ ⟨ call A B δ , ∈ideal ⟩ ⟨ ideal? , lift tt ⟩ x
--      = ⟨ ⟨ ideal? , lift tt ⟩ , call↓ ∈ideal x ↑ here ⟩
--    hon-map′ ⟨ call A B δ , ∈ideal ⟩ ⟨ real? , σ ⟩ x with map≡-implies-∈≡ (hon-≡ rc) ∈ideal
--    ... | ⟨ _ , ⟨ ∈real , refl ⟩ ⟩ = ⟨ ⟨ real? , σ ⟩ , call↓ ∈real x ↑ there here ⟩
--
--router-world-state : ∀ {ℓ} → (rc : RouterConfig {ℓ}) → Guess {ℓ} →
--  WorldState (router-world-type rc)
--router-world-state rc real? = stnode ⟨ real? , proj₁ (proj₂ (sim rc)) ⟩
--  (proj₂ (ideal rc) ∷ proj₂ (real rc) ∷ [])
--router-world-state rc ideal? = stnode ⟨ ideal? , lift tt ⟩
--  (proj₂ (ideal rc) ∷ proj₂ (real rc) ∷ [])

--router-strategy : ∀ {ℓ A} → (rc : RouterConfig {ℓ}) →
--  Strategy (proj₁ (ideal rc)) A → Strategy (router-world-type rc) A
--router-strategy = ?
--
--yggdrasil-game : ∀ {ℓ} → (rc : RouterConfig {ℓ}) →
--  Strategy (proj₁ (ideal rc)) Guess → Guess {ℓ} → ℕ → Dist (Maybe (Guess {lsuc ℓ}))
--yggdrasil-game rc str world gas =
--  (exec (router-strategy rc str) (router-world-state rc world) gas) >>=
--  (pure ∘ mmap (relevel ∘ proj₁))
