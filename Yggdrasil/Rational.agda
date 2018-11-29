module Yggdrasil.Rational where

open import Data.Bool using (true; false; T)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.GCD as GCD using (GCD; gcd)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Coprimality using (Coprime; coprime?; gcd-coprime; Bézout-coprime)
open import Data.Nat.Properties using (*-comm; *-assoc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Rational using (ℚ) renaming (_÷_ to _÷†_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sign using (Sign) renaming (+ to s+; - to s-)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; False; ⌊_⌋; fromWitness; fromWitnessFalse)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst₂; sym; cong; trans)
open Eq.≡-Reasoning using (_≡⟨_⟩_; _∎; begin_)

open ℚ

infixl 6 _+_ _-_
infixl 7 _*_ _÷_

private
  1+≢*0 : ∀ x y → suc x ≢ y ℕ.* 0
  1+≢*0 x zero ()
  1+≢*0 x (suc y) = 1+≢*0 x y

  1≢0 : ∀ {n} → suc n ≢ zero
  1≢0 ()

simp : ∀ x y-1 → ℚ
simp x y-1 with GCD.Bézout.lemma x (suc y-1)
... | GCD.Bézout.result 0 (GCD.is ⟨ _ , divides y′ y-eq ⟩ _) _ =
  ⊥-elim (1+≢*0 y-1 y′ y-eq)
... | GCD.Bézout.result (suc d-1)
      (GCD.is ⟨ divides x′ x-eq , divides y′ y-eq ⟩ _) bézout =
        _÷†_ (+ x′) y′ {fromWitness (λ {i} → Bézout-coprime bézout′)}
          {fromWitnessFalse y′≢0}
  where
    y = suc y-1
    d = suc d-1

    bézout′ : GCD.Bézout.Identity d (x′ ℕ.* d) (y′ ℕ.* d)
    bézout′ = subst₂ (GCD.Bézout.Identity d) x-eq y-eq bézout

    y′≢0 : y′ ≢ 0
    y′≢0 y′≡0 = ⊥-elim (1≢0 (trans y-eq (cong (ℕ._* d) y′≡0)))

-_ : ℚ → ℚ
- q = _÷†_ (ℤ.- numerator q) (suc (denominator-1 q))
  {fromWitness (λ{ {i} ⟨ i∣n , i∣d ⟩ → coprime q ⟨ ∣-abs⇒∣abs i (numerator q) i∣n , i∣d ⟩})}
  where
    -abs≡abs : ∀ i → ℤ.∣ ℤ.- i ∣ ≡ ℤ.∣ i ∣
    -abs≡abs (+ zero) = refl
    -abs≡abs (+ (suc n)) = refl
    -abs≡abs -[1+ n ] = refl

    ∣-abs⇒∣abs : ∀ i j → i ∣ ℤ.∣ ℤ.- j ∣ → i ∣ ℤ.∣ j ∣
    ∣-abs⇒∣abs i j (divides k j=k*i) = divides k (sym (begin
      k ℕ.* i      ≡⟨ sym j=k*i ⟩
      ℤ.∣ ℤ.- j ∣  ≡⟨ -abs≡abs j ⟩
      ℤ.∣ j ∣      ∎))
    
_÷_ : ℤ → (d : ℕ) → {d≢0 : False (d ℕ.≟ 0)} → ℚ
_÷_ n zero {}
(+ n) ÷ (suc d-1) = simp n d-1
(-[1+ n-1 ]) ÷ (suc d-1) = - simp (suc n-1) d-1

∣_∣ : ℚ → ℚ
∣ q ∣ = _÷†_ (+ ℤ.∣ numerator q ∣) (suc (denominator-1 q)) {isCoprime q}

_+_ : ℚ → ℚ → ℚ
a + b = let
    n-a = numerator a
    d-a = suc (denominator-1 a)
    n-b = numerator b
    d-b = suc (denominator-1 b)
    n-c = n-a ℤ.* (+ d-b) ℤ.+ n-b ℤ.* (+ d-a)
    d-c = d-a ℕ.* d-b
  in n-c ÷ d-c

_*_ : ℚ → ℚ → ℚ
a * b = let
    n-a = numerator a
    d-a = suc (denominator-1 a)
    n-b = numerator b
    d-b = suc (denominator-1 b)
    n-c = n-a ℤ.* n-b
    d-c = d-a ℕ.* d-b
  in n-c ÷ d-c

_-_ : ℚ → ℚ → ℚ
a - b = a + (- b)
