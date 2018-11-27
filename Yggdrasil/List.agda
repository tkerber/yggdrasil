module Yggdrasil.List where

open import Data.List using (List; _∷_; []; map)
open import Data.Product using (_×_; Σ; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _∈_ {ℓ : Level} {A : Set ℓ} : A → List A → Set ℓ where
  here : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  there : {x y : A} {xs : List A} → y ∈ xs → y ∈ (x ∷ xs)

with-proof : ∀ {ℓ} {A : Set ℓ} → (l : List A) → List (Σ A (_∈ l))
with-proof [] = []
with-proof (x ∷ xs) = ⟨ x , here ⟩ ∷ map (λ{⟨ x , ∈xs ⟩ → ⟨ x , there ∈xs ⟩})
  (with-proof xs)

head-≡ : ∀ {ℓ} {A : Set ℓ} {l₁ l₂ : List A} {x y : A} → x ∷ l₁ ≡ y ∷ l₂ → x ≡ y
head-≡ refl = refl

tail-≡ : ∀ {ℓ} {A : Set ℓ} {l₁ l₂ : List A} {x y : A} → x ∷ l₁ ≡ y ∷ l₂ →
  l₁ ≡ l₂
tail-≡ refl = refl

map≡-implies-∈≡ : ∀ {ℓ} {A B C : Set ℓ} {f₁ : A → C} {f₂ : B → C} {l₁ : List A}
  {l₂ : List B} {x : A} → map f₁ l₁ ≡ map f₂ l₂ →
  x ∈ l₁ → ∃[ y ] ((y ∈ l₂) × (f₁ x ≡ f₂ y))
map≡-implies-∈≡ {l₁ = x ∷ xs} {l₂ = []} () here
map≡-implies-∈≡ {l₁ = x ∷ xs} {l₂ = []} () (there ∈xs)
map≡-implies-∈≡ {l₁ = x ∷ xs} {l₂ = y ∷ ys} map≡ here =
  ⟨ y , ⟨ here , head-≡ map≡ ⟩ ⟩
map≡-implies-∈≡ {l₁ = x ∷ xs} {l₂ = y ∷ ys} map≡ (there ∈xs) = let
    ⟨ y , ⟨ ∈ys , x≡y ⟩ ⟩ = map≡-implies-∈≡ (tail-≡ map≡) ∈xs
  in ⟨ y , ⟨ there ∈ys , x≡y ⟩ ⟩
