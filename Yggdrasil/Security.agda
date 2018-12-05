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
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Rational using (ℚ)
open import Function using (_∘_)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Relation.Nullary.Decidable using (True; fromWitnessFalse)
open import Yggdrasil.List using (_∈_; here; there; with-proof; map≡-implies-∈≡)
open import Yggdrasil.World using (WorldType; WorldState; World; Oracle; Call; Strategy; Node; weaken; call; call↓; stnode; _∷_; []; _⊑_; Query; _∈↑_; abort; dist; _>>=_; call↯; query; path; strat; ⊤; tt; Action⊤; read; write; exec⊤; Result; out-of-gas; result; rmap; T)
open import Yggdrasil.Probability as Pr using (Dist; _>>=′_; pure; _≈[_]≈_; dmap; _*_; Pr[_[_]]≡_)
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

Actionᵣ⇒Actionᵢ : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} {σ} →
  (S : Simulator πᵢ πᵣ) → Oracle σ (World.Γ πᵣ) → ℕ →
  Action⊤ σ (World.Γ πᵣ) A → Action⊤ (σ × Simulator.state S) (World.Γ πᵢ) A
Action↯⇒Action : ∀ {ℓ : Level} {πᵢ πᵣ : World ℓ} {A : Set ℓ} {σ} →
  (S : Simulator πᵢ πᵣ) → Oracle σ (World.Γ πᵣ) → ℕ →
  Action↯ (Simulator.state S) (World.Γ πᵢ) (World.Γ πᵣ) {Simulator.hon-≡ S} A →
  Action⊤ (σ × Simulator.state S) (World.Γ πᵢ) A

private
  amap : ∀ {ℓ S Γ A B} → (A → B) → Action⊤ {ℓ} S Γ A → Action⊤ {ℓ} S Γ B
  amap f α = α >>= (λ x → dist (pure (f x)))
Actionᵣ⇒Actionᵢ S O g read = amap proj₁ read
Actionᵣ⇒Actionᵢ S O g (write σ₁) = read >>= λ { ⟨ _ , σ₂ ⟩ → write ⟨ σ₁ , σ₂ ⟩ }
Actionᵣ⇒Actionᵢ S O g (call↓ {f} ∈Γᵣ x) with map≡-implies-∈≡  
    (sym (Simulator.hon-≡ S)) ∈Γᵣ
... | ⟨ _ , ⟨ ∈Γᵢ , refl ⟩ ⟩ = call↓ ∈Γᵢ x
Actionᵣ⇒Actionᵢ _ _ _ abort = abort
Actionᵣ⇒Actionᵢ _ _ _ (dist D) = dist D
Actionᵣ⇒Actionᵢ S O g (call↯ ∈Γ Γ⊑ x) = Action↯⇒Action S O g
  (Simulator.call↯-map S ∈Γ Γ⊑ x)
Actionᵣ⇒Actionᵢ S O g (α >>= β) = (Actionᵣ⇒Actionᵢ S O g α) >>=
  Actionᵣ⇒Actionᵢ S O g ∘ β

Action↯⇒Action S O g       read            = amap proj₂ read
Action↯⇒Action S O g       (write σ₂)      = read >>= λ { ⟨ σ₁ , _ ⟩ → write ⟨ σ₁ , σ₂ ⟩ }
Action↯⇒Action S O zero    (query ∈Γ Γ⊑ x) = abort
Action↯⇒Action S O (suc g) (query ∈Γ Γ⊑ x) = Actionᵣ⇒Actionᵢ S O g (O (path Γ⊑ ∈Γ) x)
Action↯⇒Action S O g       abort           = abort
Action↯⇒Action S O g       (dist D)        = dist D
Action↯⇒Action S O g       (call↯ ∈Γ Γ⊑ x) = call↯ ∈Γ Γ⊑ x
Action↯⇒Action S O g       (α >>= β)       = (Action↯⇒Action S O g α) >>=
  Action↯⇒Action S O g ∘ β

extract-oracle : ∀ {ℓ σ πᵢ πᵣ} → (S : Simulator {ℓ} πᵢ πᵣ) →
  Oracle σ (World.Γ πᵣ) → ℕ → Oracle (σ × Simulator.state S) (World.Γ πᵢ)
extract-oracle S O g ∈Γ x = Action↯⇒Action S O g
  (query-map S ∈Γ x)
  where open Simulator

data InterestingAction {ℓ : Level} (Γ : WorldType ℓ) : Set ℓ → Set (lsuc ℓ) where
  call↓ : ∀ {f} → f ∈ (hon Γ) → (x : Call.A f) → InterestingAction Γ (Call.B f x)
  call↯ : ∀ {Γ′} {f : Call ℓ (node Γ′)} → f ∈ (adv Γ′) → Γ′ ⊑ Γ →
    (x : Call.A f) → InterestingAction Γ (Call.B f x)

toAction : ∀ {ℓ Γ A S} → InterestingAction {ℓ} Γ A → Action⊤ {ℓ} S Γ A
toAction (call↓ f∈ x) = call↓ f∈ x
toAction (call↯ ∈Γ Γ⊑ x) = call↯ ∈Γ Γ⊑ x

record _≃_ {ℓ : Level} (πᵢ πᵣ : World ℓ) :
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
    gas-map : ℕ → ℕ
    simulator : Simulator πᵢ πᵣ
    invariant : ((WorldState Γᵢ × Simulator.state simulator) × WorldState Γᵣ) → Bool
    base-case : invariant ⟨ ⟨ Σᵢ , Simulator.initial simulator ⟩ , Σᵣ ⟩ ≡ true
    proof : (g : ℕ) →
      ∀ {S} →
      (σ : S) →
      (O : Oracle S Γᵣ) →
      ∀ {A} →
      (α : InterestingAction Γᵣ A) →
      (Σ : (WorldState Γᵢ × Simulator.state simulator) × WorldState Γᵣ) →
      invariant Σ ≡ true →
        let
          Dᵢ = exec⊤ (extract-oracle simulator O (gas-map g))
            (Actionᵣ⇒Actionᵢ simulator O (gas-map g) (toAction α))
            ⟨ ⟨ σ , proj₂ (proj₁ Σ) ⟩ , proj₁ (proj₁ Σ) ⟩ (gas-map g)
          Dᵣ = exec⊤ O (toAction α) ⟨ σ , proj₂ Σ ⟩ g
          Dₛ = dmap {B = Maybe ((WorldState Γᵢ × Simulator.state simulator) × WorldState Γᵣ)} (λ
            { ⟨ abort      , _          ⟩ → nothing
            ; ⟨ out-of-gas , _          ⟩ → nothing
            ; ⟨ _          , abort      ⟩ → nothing
            ; ⟨ _          , out-of-gas ⟩ → nothing
            ; ⟨ result ⟨ _ , ⟨ ⟨ _ , σ ⟩ , Σᵢ ⟩ ⟩
              , result ⟨ _ , ⟨ _ , Σᵣ       ⟩ ⟩ ⟩ →
                just ⟨ ⟨ Σᵢ , σ ⟩ , Σᵣ ⟩
            }) (Dᵢ * Dᵣ)
        in
        -- The results are indistinguishable.
        (dmap (rmap (λ x → lift (proj₁ x))) Dᵢ Pr.≃ dmap (rmap (λ x → lift (proj₁ x))) Dᵣ) ×
        -- The resulting environment states are indistinguishable.
        (dmap (rmap (λ x → lift (proj₁ (proj₁ (proj₂ x))))) Dᵢ
            Pr.≃
         dmap (rmap (λ x → lift (proj₁ (proj₂ x)))) Dᵣ) ×
        -- And any resulting system states are in the invariant.
        (Pr[ (λ { nothing → ⊤; (just x) → T (invariant x) }) [ Dₛ ]]≡ 1)
