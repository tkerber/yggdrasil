module Yggdrasil.Security where

open import Agda.Builtin.FromNat using (Number)
import Data.Nat.Literals as ℕLit
import Data.Rational.Literals as ℚLit
import Data.Integer.Literals as ℤLit
open import Data.Bool using (Bool; true; false)
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
open import Yggdrasil.World using (WorldType; WorldState; World; Oracle; Call; Strategy; Node; Action; weaken; call; call↓; _↑_; stnode; _∷_; []; ⌊exec⌋; _⊑_; Query; _∈↑_; abort; dist; _>>=_; call↯; query; path; _↑; strat; ⊤; tt; Action↓; exec↓)
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
    {hon-≡ : map weaken (hon Γᵢ) ≡ map weaken (hon Γᵣ)} : Set ℓ →
    Set (lsuc ℓ) where
  read  : Action↯ σ Γᵢ Γᵣ σ
  write : σ → Action↯ σ Γᵢ Γᵣ ⊤
  query : ∀ {Γ′ q} → q ∈ qry (node Γ′) → Γ′ ⊑ Γᵣ → (x : Query.A q) → Action↯ σ Γᵢ Γᵣ (Query.B q x)
  abort : ∀ {A} → Action↯ σ Γᵢ Γᵣ A
  dist  : ∀ {A} → Dist A → Action↯ σ Γᵢ Γᵣ A
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γᵢ → (x : Call.A f) →
    Action↯ σ Γᵢ Γᵣ (Call.B f x)
  _>>=_ : ∀ {A B} → Action↯ σ Γᵢ Γᵣ {hon-≡} A → (A → Action↯ σ Γᵢ Γᵣ {hon-≡} B) →
    Action↯ σ Γᵢ Γᵣ B

-- FIXME: Am I an idiot? Shouldn't the simulator map attacks against *real*
-- protocols to attacks against *ideal* protocols?
record Simulator {ℓ : Level} (πᵢ πᵣ : World ℓ) : Set (lsuc ℓ) where
  Γᵢ : WorldType ℓ
  Γᵢ = World.Γ πᵢ
  Γᵣ : WorldType ℓ
  Γᵣ = World.Γ πᵣ
  field
    hon-≡ : map weaken (hon Γᵢ) ≡ map weaken (hon Γᵣ)
    state : Set ℓ
    initial : state
    call↯-map : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γᵣ →
      (x : Call.A f) → Action↯ state Γᵢ Γᵣ {hon-≡} (Call.B f x)
    query-map : ∀ {q} → q ∈↑ Γᵢ → (x : Query.A q) → Action↯ state Γᵢ Γᵣ {hon-≡} (Query.B q x)

Actionᵣ⇒Actionᵢ : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} →
  (S : Simulator πᵢ πᵣ) → Oracle (World.Γ πᵣ) → Simulator.state S → ℕ →
  Action (World.Γ πᵣ) A → Action (World.Γ πᵢ) (A × Simulator.state S)
Action↯⇒Action : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} →
  (S : Simulator πᵢ πᵣ) → Oracle (World.Γ πᵣ) → Simulator.state S → ℕ →
  Action↯ (Simulator.state S) (World.Γ πᵢ) (World.Γ πᵣ) {Simulator.hon-≡ S} A →
  Action (World.Γ πᵢ) (A × Simulator.state S)

private
  with-state : ∀ {ℓ Γ A Σ} → Σ → A → Action {ℓ} Γ (A × Σ)
  with-state σ x = dist (pure ⟨ x , σ ⟩)

  without-state : ∀ {ℓ Γ} {A Σ : Set ℓ} → (A × Σ) → Action {ℓ} Γ A
  without-state ⟨ x , _ ⟩ = dist (pure x)

-- WAIT -- Does the state actually properly survive?
-- FIXME: No, it doesn't. This is probably *unavoidable* without adding state
-- to the execution definition. Do this.
Actionᵣ⇒Actionᵢ _ _ _ zero _ = abort
Actionᵣ⇒Actionᵢ S O σ (suc g) ((call↓ {f} ∈Γᵣ x) ↑) with map≡-implies-∈≡  
    (sym (Simulator.hon-≡ S)) ∈Γᵣ
... | ⟨ _ , ⟨ ∈Γᵢ , refl ⟩ ⟩ = call↓ ∈Γᵢ x ↑ >>= with-state σ
Actionᵣ⇒Actionᵢ _ _ _ _ abort = abort
Actionᵣ⇒Actionᵢ _ _ σ _ (dist D) = dist D >>= with-state σ
Actionᵣ⇒Actionᵢ S O σ (suc g) (call↯ ∈Γ Γ⊑ x) = Action↯⇒Action S O σ g
  (Simulator.call↯-map S ∈Γ Γ⊑ x)
Actionᵣ⇒Actionᵢ S O σ (suc g) (α >>= β) = (Actionᵣ⇒Actionᵢ S O σ (suc g) α) >>=
  λ{ ⟨ x , σ′ ⟩ → Actionᵣ⇒Actionᵢ S O σ′ g (β x) }

Action↯⇒Action _ _ _ zero _ = abort
Action↯⇒Action S O σ _ read = dist (pure ⟨ σ , σ ⟩)
Action↯⇒Action S O _ _ (write σ) = dist (pure ⟨ tt , σ ⟩)
Action↯⇒Action S O σ (suc g) (query ∈Γ Γ⊑ x) = Actionᵣ⇒Actionᵢ S O σ g (O (path Γ⊑ ∈Γ) x)
Action↯⇒Action _ _ _ _ abort = abort
Action↯⇒Action _ _ σ _ (dist D) = dist D >>= with-state σ
Action↯⇒Action _ _ σ _ (call↯ ∈Γ Γ⊑ x) = call↯ ∈Γ Γ⊑ x >>= with-state σ
Action↯⇒Action S O σ (suc g) (α >>= β) = (Action↯⇒Action S O σ (suc g) α) >>= λ{
    ⟨ x , σ′ ⟩ → Action↯⇒Action S O σ′ g (β x)
  }

extract-oracle : ∀ {ℓ πᵢ πᵣ} → Simulator {ℓ} πᵢ πᵣ → Oracle (World.Γ πᵣ) → ℕ →
  Oracle (World.Γ πᵢ)
extract-oracle S O g ∈Γ x = Action↯⇒Action S O (initial S) g
  (Simulator.query-map S ∈Γ x) >>= without-state
  where open Simulator

simulated-strategy : ∀ {ℓ πᵢ πᵣ A} → Simulator {ℓ} πᵢ πᵣ →
  Strategy (World.Γ πᵣ) A → ℕ → Strategy (World.Γ πᵢ) A
simulated-strategy S str g = strat
  (Actionᵣ⇒Actionᵢ S (oracle str) (initial S) g (init str) >>= without-state)
  (extract-oracle S (oracle str) g)
  where open Simulator

record Adv[_,_]≤_ {ℓ : Level} (πᵢ πᵣ : World ℓ) (ε : ℚ) :
    Set (lsuc (lsuc ℓ)) where
  Γᵣ : WorldType ℓ
  Γᵣ = World.Γ πᵣ
  Γᵢ : WorldType ℓ
  Γᵢ = World.Γ πᵢ
  Σᵣ : WorldState Γᵣ
  Σᵣ = World.Σ πᵣ
  Σᵢ : WorldState Γᵢ
  Σᵢ = World.Σ πᵢ
  field
    sim-gas : ℕ
    gas-map : ℕ → ℕ
    simulator : Simulator πᵢ πᵣ
    invariant : (WorldState Γᵢ × WorldState Γᵣ) × Simulator.state simulator → Bool
    base-case : invariant ⟨ ⟨ Σᵢ , Σᵣ ⟩ , Simulator.initial simulator ⟩ ≡ true
    proof : (g : ℕ) → (O : Oracle Γᵣ) → ∀ {A} → (α : Action↓ Γᵣ A) →
      (Σ : ((WorldState Γᵢ × WorldState Γᵣ) × Simulator.state simulator)) →
      invariant Σ ≡ true → 
      let
        dᵢ = exec↓ (extract-oracle simulator O sim-gas)
          (Actionᵣ⇒Actionᵢ simulator O (proj₂ Σ) sim-gas α)
          (proj₁ (proj₁ Σ)) here g
      in ?
      

--Actionᵣ⇒Actionᵢ : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} →
--  (S : Simulator πᵢ πᵣ) → Oracle (World.Γ πᵣ) → Simulator.state S → ℕ →
--  Action (World.Γ πᵣ) A → Action (World.Γ πᵢ) (A × Simulator.state S)


--      (str : Strategy Γᵣ Guess) →
--      (⌊exec⌋ (simulated-strategy simulator str (sim-gas str)) (World.Σ πᵢ)
--        (gas-map g))
--        ≈[ ε ]≈
--      (⌊exec⌋ str (World.Σ πᵣ) g)

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
