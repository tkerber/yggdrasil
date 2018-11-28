module Yggdrasil.Rational where

open import Data.Bool using (true; false; T)
open import Data.Integer using (ℤ; ∣_∣; _◃_; sign; +_) renaming (_+_ to _ℤ+_; _*_ to _ℤ*_)
open import Data.Nat as ℕ using (ℕ; suc; zero) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.GCD using (GCD; gcd)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Coprimality using (coprime?; gcd-coprime)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Rational using (ℚ; _÷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sign using (Sign) renaming (+ to s+; - to s-)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; False; ⌊_⌋; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open ℚ

¬0*¬0≡¬0 : {a b : ℕ} → ¬ (a ≡ 0) → ¬ (b ≡ 0) → ¬ (a ℕ* b ≡ 0)
¬0*¬0≡¬0 = ?

¬0≡¬0*¬0 : {a b : ℕ} → ¬ (0 ≡ a ℕ* b) → ¬ (b ≡ 0)
¬0≡¬0*¬0 = ?

_+_ : ℚ → ℚ → ℚ
a + b with gcd (suc (denominator-1 a)) (suc (denominator-1 b))
... | ⟨ c , denom-gcd ⟩ with GCD.commonDivisor denom-gcd
...   | ⟨ divides d₁ d₁*c≡da , divides d₂ d₂*c≡db ⟩ = let
        d′ = d₁ ℕ* d₂ ℕ* c
        n′ = ((numerator a) ℤ* (+ d₂)) ℤ+ ((numerator b) ℤ* (+ d₁))
        d′≢0 = ?
      in _÷_ n′ d′
        {fromWitness (λ{ {i} ⟨ i∣n′ , i∣d′ ⟩ → 
          -- Coprime because: d₁ coprime d₂, d₁ coprime n₁, d₂ coprime n₂, n₁,
          -- n₂ coprime c
          ?})}
        {?}


_*_ : ℚ → ℚ → ℚ
a * b = ?

_-_ : ℚ → ℚ → ℚ
a - b = ?

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
