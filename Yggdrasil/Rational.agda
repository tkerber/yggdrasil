module Yggdrasil.Rational where

open import Data.Bool using (true; false; T)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.GCD as GCD using (GCD; gcd)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Coprimality using (coprime?; gcd-coprime; Bézout-coprime)
open import Data.Nat.Properties using (*-comm; *-assoc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Rational using (ℚ) renaming (_÷_ to _÷†_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sign using (Sign) renaming (+ to s+; - to s-)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; False; ⌊_⌋; fromWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst₂; sym; cong)
open Eq.≡-Reasoning using (_≡⟨_⟩_; _∎; begin_)

open ℚ

infixl 6 _+_ _-_
infixl 7 _*_ _÷_

1+≢*0 : ∀ x y → suc x ≢ y ℕ.* 0
1+≢*0 x zero ()
1+≢*0 x (suc y) = 1+≢*0 x y

simp : ∀ x y-1 → ℚ
simp x y-1 with GCD.Bézout.lemma x (suc y-1)
... | GCD.Bézout.result 0 (GCD.is ⟨ _ , divides y′ y-eq ⟩ _) _ = ⊥-elim (1+≢*0 y-1 y′ y-eq)
... | GCD.Bézout.result (suc d-1) (GCD.is ⟨ divides x′ x-eq , divides y′ y-eq ⟩ _) bézout = _÷†_ (+ x′) y′ {fromWitness {!(Bézout-coprime bézout′)!}}
  where
    y = suc y-1
    d = suc d-1

    bézout′ : GCD.Bézout.Identity d (x′ ℕ.* d) (y′ ℕ.* d)
    bézout′ = subst₂ (GCD.Bézout.Identity d) x-eq y-eq bézout

    eq-prf : x ℕ.* y′ ≡ x′ ℕ.* y
    eq-prf = begin
      x ℕ.* y′           ≡⟨ cong (λ z → z ℕ.* y′) x-eq ⟩
      x′ ℕ.* d ℕ.* y′    ≡⟨ *-assoc x′ d y′ ⟩
      x′ ℕ.* (d ℕ.* y′)  ≡⟨ sym (cong (ℕ._*_ x′) (*-comm y′ d)) ⟩
      x′ ℕ.* (y′ ℕ.* d)  ≡⟨ sym (cong (ℕ._*_ x′) y-eq)  ⟩
      x′ ℕ.* y           ∎

postulate
  _÷_ : ℤ → (d : ℕ) → {d≢0 : False (d ℕ.≟ 0)} → ℚ

∣_∣ : ℚ → ℚ
∣ q ∣ = _÷†_ (+ ℤ.∣ numerator q ∣) (suc (denominator-1 q)) {isCoprime q}

-_ : ℚ → ℚ
- q = _÷_ (ℤ.- numerator q) (suc (denominator-1 q))

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


--gcd (suc (denominator-1 a)) (suc (denominator-1 b))
--... | ⟨ c , denom-gcd ⟩ with GCD.commonDivisor denom-gcd
--...   | ⟨ divides d₁ d₁*c≡da , divides d₂ d₂*c≡db ⟩ = let
--        d′ = d₁ ℕ* d₂ ℕ* c
--        n′ = ((numerator a) ℤ* (+ d₂)) ℤ+ ((numerator b) ℤ* (+ d₁))
--        d′≢0 = ?
--      in _÷_ n′ d′
--        {fromWitness (λ{ {i} ⟨ i∣n′ , i∣d′ ⟩ → 
--          -- Coprime because: d₁ coprime d₂, d₁ coprime n₁, d₂ coprime n₂, n₁,
--          -- n₂ coprime c
--          ?})}
--        {?}



--data ℚ′ : Set where
--  _÷′_ : ℤ → (d : ℕ) → {d≢0 : False (d ℕ.≟ 0)} → ℚ′
--
--∣◃∣-≡ : (n : ℕ) → (s : Sign) → ∣ s ◃ n ∣ ≡ n
--∣◃∣-≡ = ?
--
--normalise : ℚ′ → ℚ
--normalise (_÷′_ n zero {()})
--normalise (n ÷′ suc d) with gcd ∣ n ∣ (suc d)
----... | ⟨ 1 , gcd ⟩ = record
----  { numerator = n
----  ; denominator-1 = d
----  ; isCoprime = fromWitness {Q = coprime? ∣ n ∣ (suc d)} (gcd-coprime gcd) }
--... | ⟨ _ , gcd₁ ⟩ with GCD.commonDivisor gcd₁
--...   | ⟨ divides n′ _ , divides d′ _ ⟩ with d′ | gcd n′ d′ | sign n
--...     | suc d′ | ⟨ suc (suc m) , gcd₂ ⟩ | _ = ?
--...     | suc d′ | ⟨ 1 , gcd₂ ⟩ | s+ = record
--            { numerator = + n′
--            ; denominator-1 = d′
--            ; isCoprime = fromWitness {Q = coprime? n′ (suc d′)} (gcd-coprime gcd₂) }
--with coprime? ∣ n ∣ (suc d)
--... | yes cp = record
--  { numerator = n
--  ; denominator-1 = d
--  ; isCoprime = fromWitness {Q = coprime? ∣ n ∣ (suc d)} cp }
--... | no ¬cp = ?
