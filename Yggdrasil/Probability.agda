module Yggdrasil.Probability where

open import Agda.Builtin.FromNat using (Number)
import Data.Nat.Literals as ℕLit
import Data.Rational.Literals as ℚLit
import Data.Integer.Literals as ℤLit
open import Data.List using (List; _∷_; []; map; filter; length; foldr)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; _-_) renaming (_*_ to _ℤ*_)
open import Data.Nat using (ℕ; zero; suc; s≤s) renaming (_*_ to _ℕ*_; _≤?_ to _ℕ≤?_; _≤_ to _ℕ≤_)
open import Data.Nat.Literals
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.List.Properties using (length-filter; length-map)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Rational using (ℚ) renaming (_≤?_ to _ℚ≤?_; _≤_ to _ℚ≤_)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Level using (Level; Lift; lower; _⊔_) renaming (suc to lsuc; lift to llift)
open import Yggdrasil.List using (_∈_; with-proof)
import Yggdrasil.Rational as ℚ

instance
  ℕnumber : Number ℕ
  ℕnumber = ℕLit.number
  ℤnumber : Number ℤ
  ℤnumber = ℤLit.number
  ℚnumber : Number ℚ
  ℚnumber = ℚLit.number

case : ℚ → ℚ → ℚ → ℚ
case Pr[A] Pr[B∣A] Pr[B∣¬A] = Pr[A] ℚ.* Pr[B∣A] ℚ.+ (1 ℚ.- Pr[A]) ℚ.* Pr[B∣¬A]

sum : List ℚ → ℚ
sum = foldr (ℚ._+_) 0

PrFin : ∀ {ℓ} → ℕ → Set ℓ
PrFin {ℓ} n = Lift ℓ (Fin (suc (suc n)))

all-fin : (n : ℕ) → List (Fin n)
all-fin zero = []
all-fin (suc n) = zero ∷ map suc (all-fin n)

length-all-fin : (n : ℕ) → length (all-fin n) ≡ n
length-all-fin zero = refl
length-all-fin (suc n) = cong suc (trans (length-map suc (all-fin n)) (length-all-fin n))

count : ∀ {ℓ n} {P : PrFin {ℓ} n → Set ℓ} → ((f : PrFin {ℓ} n) → Dec (P f)) → ℕ
count {n = n} dec = length (filter dec (map llift (all-fin (suc (suc n)))))

data Dist {ℓ : Level} : Set ℓ → Set (lsuc ℓ) where
  pure : ∀ {A : Set ℓ} → A → Dist A
  sample : ∀ {n : ℕ} → Dist (PrFin {ℓ} n)
  _>>=_ : ∀ {A B : Set ℓ} → Dist A → (A → Dist B) → Dist B

dmap : ∀ {ℓ A B} → (A → B) → Dist {ℓ} A → Dist {ℓ} B
dmap f d = d >>= (λ x → pure (f x))

_*_ : ∀ {ℓ A B} → Dist {ℓ} A → Dist {ℓ} B → Dist {ℓ} (A × B)
a * b = a >>= (λ x → b >>= (λ y → pure ⟨ x , y ⟩))

lift : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} → Dist A → Dist (Lift ℓ₂ A)
lift (pure x) = pure (llift x)
lift {ℓ₁} {ℓ₂} (sample {n = n}) = sample {n = n} >>=
  (pure ∘ llift ∘ llift ∘ lower)
lift {ℓ₂ = ℓ} (D >>= f) = lift {ℓ₂ = ℓ} D >>= (lift ∘ f ∘ lower)

≡⇒≤ : {a b : ℕ} → a ≡ b → a ℕ≤ b
≡⇒≤ refl = ≤-refl

data Pr[_[_]]≡_ {ℓ : Level} : {A : Set ℓ} → (P : A → Set ℓ) → Dist A →
    ℚ → Set (lsuc ℓ) where
  pure-zero : {A : Set ℓ} {P : A → Set ℓ} → (x : A) → ¬ (P x) →
    Pr[ P [ pure x ]]≡ 0
  pure-one : {A : Set ℓ} {P : A → Set ℓ} → (x : A) → P x →
    Pr[ P [ pure x ]]≡ 1
  sample-count : {n : ℕ} {P : PrFin n → Set ℓ} →
    (dec : (f : PrFin n) → Dec (P f)) →
    Pr[ P [ sample {n = n} ]]≡ (+ (count dec) ℚ.÷ (suc (suc n)))
  conditional : {A B : Set ℓ} {D : Dist A} {f : A → Dist B} {P₁ : A → Set ℓ}
    {P₂ : B → Set ℓ} {p₁ p₂ p₃ : ℚ} →
    Pr[ P₁ [ D ]]≡ p₁ → 
    ((x : A) → P₁ x → Pr[ P₂ [ f x ]]≡ p₂) →
    ((x : A) → ¬ (P₁ x) → Pr[ P₂ [ f x ]]≡ p₃) → 
    Pr[ P₂ [ D >>= f ]]≡ (case p₁ p₂ p₃)

record _≈[_]≈_ {ℓ : Level} {A : Set ℓ} (d₁ : Dist A) (ε : ℚ) (d₂ : Dist A) : Set (lsuc ℓ) where
  field
    elements : List A
    pr₁ : (x : A) → x ∈ elements → ∃[ p ] Pr[ _≡ x [ d₁ ]]≡ p
    pr₂ : (x : A) → x ∈ elements → ∃[ p ] Pr[ _≡ x [ d₂ ]]≡ p
    elements-complete-d₁ : sum (map (λ{
        ⟨ x , x∈xs ⟩ → proj₁ (pr₁ x x∈xs)
      }) (with-proof elements)) ≡ 1
    elements-complete-d₂ : sum (map (λ{
        ⟨ x , x∈xs ⟩ → proj₁ (pr₂ x x∈xs)
      }) (with-proof elements)) ≡ 1
    ε-error : sum (map (λ{
        ⟨ x , x∈xs ⟩ → ℚ.∣ proj₁ (pr₁ x x∈xs) ℚ.- proj₁ (pr₂ x x∈xs) ∣
      }) (with-proof elements)) ℚ≤ ε

_≃_ : {ℓ : Level} {A : Set ℓ} (d₁ d₂ : Dist A) → Set (lsuc ℓ)
d₁ ≃ d₂ = d₁ ≈[ 0 ]≈ d₂

postulate
  ≈-trans : {ℓ : Level} {A : Set ℓ} {d₁ d₂ d₃ : Dist A} {ε₁ ε₂ : ℚ} →
    d₁ ≈[ ε₁ ]≈ d₂ → d₂ ≈[ ε₂ ]≈ d₃ → d₁ ≈[ ε₁ ℚ.+ ε₂ ]≈ d₃
  ≈-sym : {ℓ : Level} {A : Set ℓ} {d₁ d₂ : Dist A} {ε : ℚ} → d₁ ≈[ ε ]≈ d₂ →
    d₂ ≈[ ε ]≈ d₁
  ≈-refl : {ℓ : Level} {A : Set ℓ} {d : Dist A} → d ≃ d
