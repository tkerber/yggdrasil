module Yggdrasil.Probability where

open import Data.List using (List; _∷_; []; map; filter; length)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (+_; _-_) renaming (_*_ to _ℤ*_)
open import Data.Nat using (ℕ; zero; suc) renaming (_*_ to _ℕ*_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Rational using (ℚ; _÷_; _≤?_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True)
open import Level using (Level; Lift; lift) renaming (suc to lsuc)

data [0,1] : Set where
  interval : (q : ℚ) → {≤1 : True (q ≤? (+ 1 ÷ 1))} {0≤ : True ((+ 0 ÷ 1) ≤? q)} → [0,1]

1-_ : [0,1] → [0,1]
1- (interval q {q≤1} {0≤q}) = let
    n = ℚ.numerator q
    d = suc (ℚ.denominator-1 q)
    n′ = + d - n
    n′∣̷d = ?
    1-q = _÷_ n′ d {n′∣̷d}
    1-q≤1 = ?
    0≤1-q = ?
  in interval 1-q {1-q≤1} {0≤1-q}

_*_ : [0,1] → [0,1] → [0,1]
(interval q₁ {q₁≤1} {0≤q₁}) * (interval q₂ {q₂≤1} {0≤q₂}) = let
    n₁ = ℚ.numerator q₁
    n₂ = ℚ.numerator q₂
    d₁ = suc (ℚ.denominator-1 q₁)
    d₂ = suc (ℚ.denominator-1 q₂)
    n′ = n₁ ℤ* n₂
    d′ = d₁ ℕ* d₂
    q₁*q₂ = ?
    q₁*q₂≤1 = ?
    0≤q₁*q₂ = ?
  in interval q₁*q₂ {q₁*q₂≤1} {0≤q₁*q₂}

case : [0,1] → [0,1] → [0,1] → [0,1]
case = ?

_/_ : ℕ → ℕ → [0,1]
_/_ = ?

PrFin : ∀ {ℓ} → ℕ → Set ℓ
PrFin {ℓ} n = Lift ℓ (Fin (suc (suc n)))

all-fin : (n : ℕ) → List (Fin n)
all-fin zero = []
all-fin (suc n) = zero ∷ map suc (all-fin n)

count : ∀ {ℓ n} {P : PrFin {ℓ} n → Set ℓ} → ((f : PrFin {ℓ} n) → Dec (P f)) → ℕ
count {n = n} dec = length (filter dec (map lift (all-fin (suc (suc n)))))

data Dist {ℓ : Level} : Set ℓ → Set (lsuc ℓ) where
  pure : ∀ {A : Set ℓ} → A → Dist A
  sample : ∀ {n : ℕ} → Dist (PrFin n)
  bind : ∀ {A B : Set ℓ} → Dist A → (A → Dist B) → Dist B

data Pr[_[_]]≡_ {ℓ : Level} : {A : Set ℓ} → (P : A → Set ℓ) → Dist A →
    [0,1] → Set (lsuc ℓ) where
  pure-zero : {A : Set ℓ} {P : A → Set ℓ} → (x : A) → ¬ (P x) →
    Pr[ P [ pure x ]]≡ (interval (+ 0 ÷ 1))
  pure-one : {A : Set ℓ} {P : A → Set ℓ} → (x : A) → P x →
    Pr[ P [ pure x ]]≡ (interval (+ 1 ÷ 1))
  sample-count : {n : ℕ} {P : PrFin n → Set ℓ} →
    (dec : (f : PrFin n) → Dec (P f)) →
    Pr[ P [ sample {n = n} ]]≡ (count dec / suc (suc n))
  conditional : {A B : Set ℓ} {D : Dist A} {f : A → Dist B} {P₁ : A → Set ℓ}
    {P₂ : B → Set ℓ} {p₁ p₂ p₃ : [0,1]} →
    Pr[ P₁ [ D ]]≡ p₁ → 
    ((x : A) → P₁ x → Pr[ P₂ [ f x ]]≡ p₂) →
    ((x : A) → ¬ (P₁ x) → Pr[ P₂ [ f x ]]≡ p₃) → 
    Pr[ P₂ [ bind D f ]]≡ (case p₁ p₂ p₃)
