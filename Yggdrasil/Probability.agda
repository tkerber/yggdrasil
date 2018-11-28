module Yggdrasil.Probability where

open import Data.List using (List; _∷_; []; map; filter; length)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (+_; _-_) renaming (_*_ to _ℤ*_)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s) renaming (_*_ to _ℕ*_; _≤?_ to _ℕ≤?_)
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.List.Properties using (length-filter; length-map)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Rational using (ℚ; _÷_) renaming (_≤?_ to _ℚ≤?_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)
open import Yggdrasil.List using (_∈_; with-proof)

record [0,1] : Set where
  field
    q : ℚ
    ≤1 : True (q ℚ≤? (+ 1 ÷ 1))
    0≤ : True ((+ 0 ÷ 1) ℚ≤? q)

interval : (q : ℚ) → {≤1 : True (q ℚ≤? (+ 1 ÷ 1))} →
  {0≤ : True ((+ 0 ÷ 1) ℚ≤? q)} → [0,1]
interval q {≤1} {0≤} = record { q = q; ≤1 = ≤1; 0≤ = 0≤ }

postulate
  _ℚ+_ : ℚ → ℚ → ℚ
  1-_ : [0,1] → [0,1]
  _*_ : [0,1] → [0,1] → [0,1]
  case : [0,1] → [0,1] → [0,1] → [0,1]
  _/_ : (n : ℕ) → (m : ℕ) → {n≤m : True (n ℕ≤? m)} → [0,1]
  sum-[0,1] : List [0,1] → ℚ
  -- Absolute difference
  _δ_ : [0,1] → [0,1] → [0,1]

PrFin : ∀ {ℓ} → ℕ → Set ℓ
PrFin {ℓ} n = Lift ℓ (Fin (suc (suc n)))

all-fin : (n : ℕ) → List (Fin n)
all-fin zero = []
all-fin (suc n) = zero ∷ map suc (all-fin n)

length-all-fin : (n : ℕ) → length (all-fin n) ≡ n
length-all-fin zero = refl
length-all-fin (suc n) = cong suc (trans (length-map suc (all-fin n)) (length-all-fin n))

count : ∀ {ℓ n} {P : PrFin {ℓ} n → Set ℓ} → ((f : PrFin {ℓ} n) → Dec (P f)) → ℕ
count {n = n} dec = length (filter dec (map lift (all-fin (suc (suc n)))))

data Dist {ℓ : Level} : Set ℓ → Set (lsuc ℓ) where
  pure : ∀ {A : Set ℓ} → A → Dist A
  sample : ∀ {n : ℕ} → Dist (PrFin n)
  bind : ∀ {A B : Set ℓ} → Dist A → (A → Dist B) → Dist B

≡⇒≤ : {a b : ℕ} → a ≡ b → a ≤ b
≡⇒≤ refl = ≤-refl

data Pr[_[_]]≡_ {ℓ : Level} : {A : Set ℓ} → (P : A → Set ℓ) → Dist A →
    [0,1] → Set (lsuc ℓ) where
  pure-zero : {A : Set ℓ} {P : A → Set ℓ} → (x : A) → ¬ (P x) →
    Pr[ P [ pure x ]]≡ (interval (+ 0 ÷ 1))
  pure-one : {A : Set ℓ} {P : A → Set ℓ} → (x : A) → P x →
    Pr[ P [ pure x ]]≡ (interval (+ 1 ÷ 1))
  sample-count : {n : ℕ} {P : PrFin n → Set ℓ} →
    (dec : (f : PrFin n) → Dec (P f)) →
    Pr[ P [ sample {n = n} ]]≡ (_/_ (count dec) (suc (suc n)) {fromWitness (
      ≤-trans (length-filter dec (map lift (all-fin (suc (suc n)))))
      (s≤s (s≤s (≡⇒≤
        (trans (length-map lift (map suc (map suc (all-fin n))))
        (trans (length-map suc (map suc (all-fin n)))
        (trans (length-map suc (all-fin n)) (length-all-fin n)))))))
    )})
  conditional : {A B : Set ℓ} {D : Dist A} {f : A → Dist B} {P₁ : A → Set ℓ}
    {P₂ : B → Set ℓ} {p₁ p₂ p₃ : [0,1]} →
    Pr[ P₁ [ D ]]≡ p₁ → 
    ((x : A) → P₁ x → Pr[ P₂ [ f x ]]≡ p₂) →
    ((x : A) → ¬ (P₁ x) → Pr[ P₂ [ f x ]]≡ p₃) → 
    Pr[ P₂ [ bind D f ]]≡ (case p₁ p₂ p₃)

data _≈[_]≈_ {ℓ : Level} {A : Set ℓ} : Dist A → ℚ → Dist A → Set (lsuc ℓ) where
  finite : (d₁ d₂ : Dist A) → (xs : List A) →
    (pr₁ : (x : A) → x ∈ xs → ∃[ p ] Pr[ _≡ x [ d₁ ]]≡ p) →
    (pr₂ : (x : A) → x ∈ xs → ∃[ p ] Pr[ _≡ x [ d₂ ]]≡ p) →
    (ε : ℚ) →
    sum-[0,1] (map (λ{
      ⟨ x , x∈xs ⟩ → proj₁ (pr₁ x x∈xs)
    }) (with-proof xs)) ≡ + 1 ÷ 1 →
    sum-[0,1] (map (λ{
      ⟨ x , x∈xs ⟩ → proj₁ (pr₂ x x∈xs)
    }) (with-proof xs)) ≡ + 1 ÷ 1 →
    sum-[0,1] (map (λ{
      ⟨ x , x∈xs ⟩ → proj₁ (pr₁ x x∈xs) δ proj₁ (pr₂ x x∈xs)
    }) (with-proof xs)) ≡ ε →
    d₁ ≈[ ε ]≈ d₂
