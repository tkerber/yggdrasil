module Yggdrasil.Examples.SecureChannel where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_*_; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Level using (Level; Lift; lift)
open import Relation.Binary.PropositionalEquality using (refl)
open import Yggdrasil.World
open import Yggdrasil.List
open import Yggdrasil.Security
open import Yggdrasil.Probability using (pure)

open Action↑
open Action↯
open WorldStates

πᵢ-SecureChannel : {ℓ : Level} → (M L : Set ℓ) → (M → L) → World ℓ
πᵢ-SecureChannel M L l = record
  { Γ = record
    { node = mknode (Maybe M) [] (mknquery L ⊤ ∷ [])
    ; adv  = []
    ; hon  =
      ncall ⊤ (Maybe M) (λ _ → read) ∷
      ncall M ⊤ (λ m → write (just m) >> query here (l m) >> return tt) ∷
      []
    }
  ; Σ = stnode nothing []
  }

πᵢ-AuthChannel : {ℓ : Level} → Set ℓ → World ℓ
πᵢ-AuthChannel M = record
  { Γ = record
    { node = mknode (Maybe M) [] (mknquery M ⊤ ∷ [])
    ; adv  = []
    ; hon  =
      ncall ⊤ (Maybe M) (λ _ → read) ∷
      ncall M ⊤ (λ m → write (just m) >> query here m >> return tt) ∷
      []
    }
  ; Σ = stnode nothing []
  }

πᵢ-PKE : {ℓ : Level} → (M C PK L : Set ℓ) → (M → L) → (PK → PK → Bool) →
  (C → C → Bool) → World ℓ
πᵢ-PKE M C PK L l pk?= c?= = record
  { Γ = record
    { node = mknode (Maybe (PK × List (M × C))) []
      (mknquery L C ∷ mknquery ⊤ PK ∷ [])
    ; adv  = []
    ; hon  =
      ncall C (Maybe M) (λ c → read >>= λ
        { nothing            → return nothing
        ; (just ⟨ _ , log ⟩) → return (in-log c log)
        }) ∷
      ncall (PK × M) (Maybe C) (λ{ ⟨ pk′ , m ⟩ → read >>= λ
        { nothing             → return nothing
        ; (just ⟨ pk , log ⟩) → if pk?= pk pk′ then
          query here (l m) >>=
            (λ c → write (just ⟨ pk , ⟨ m , c ⟩ ∷ log ⟩) >>
            return (just c)) else
          return nothing
        }}) ∷
      ncall ⊤ PK (λ _ → query (there here) tt >>=
        (λ pk → write (just ⟨ pk , [] ⟩) >> return pk)) ∷
      []
    }
  ; Σ = stnode nothing []
  }
  where
    in-log : C → List (M × C) → Maybe M
    in-log c [] = nothing
    in-log c (⟨ m , c′ ⟩ ∷ log) = if c?= c c′ then just m else in-log c log

πᵣ-SecureChannel : {ℓ : Level} → (M C PK L : Set ℓ) → (M → L) →
  (PK → PK → Bool) → (C → C → Bool) → World ℓ
πᵣ-SecureChannel M C PK L l pk?= c?= = record
  { Γ = record
    { node = mknode (Maybe PK) (
        World.Γ (πᵢ-PKE M C PK L l pk?= c?=) ∷
        World.Γ (πᵢ-AuthChannel C) ∷
        [])
      []
    ; adv  = []
    ; hon  =
      ncall ⊤ (Maybe M) (λ _ → call↓ here (there here) tt >>= λ
        { nothing  → return nothing
        ; (just c) → call↓ here here c
        }) ∷
      ncall M ⊤ (λ m → let
          doSend = λ pk m → call↓ (there here) here ⟨ pk , m ⟩ >>= (λ
           { nothing → abort -- The public key we set was refused!
           ; (just c) → call↓ (there here) (there here) c
           })
        in read >>= λ
          { nothing   → call↓ (there (there here)) here tt >>= (λ pk →
              write (just pk) >> doSend pk m)
          ; (just pk) → doSend pk m
          }) ∷
      []
    }
  ; Σ = stnode nothing (
    World.Σ (πᵢ-PKE M C PK L l pk?= c?=) ∷
    World.Σ (πᵢ-AuthChannel C) ∷
    [])
  }

BitString : ∀ {ℓ} → Set ℓ
BitString {ℓ} = Lift ℓ (List Bool)

bitstring?= : ∀ {ℓ} → BitString {ℓ} → BitString {ℓ} → Bool
bitstring?= (lift []) (lift []) = true
bitstring?= (lift (_ ∷ _)) (lift []) = false
bitstring?= (lift []) (lift (_ ∷ _)) = false
bitstring?= {ℓ} (lift (true  ∷ xs)) (lift (true  ∷ ys)) = bitstring?= {ℓ} (lift xs) (lift ys)
bitstring?= {ℓ} (lift (false ∷ xs)) (lift (false ∷ ys)) = bitstring?= {ℓ} (lift xs) (lift ys)
bitstring?= (lift (true  ∷ xs)) (lift (false ∷ ys)) = false
bitstring?= (lift (false ∷ xs)) (lift (true  ∷ ys)) = false

_>>↯_ : ∀ {ℓ Σ Γᵢ Γᵣ A B hon-≡} → Action↯ {ℓ} Σ Γᵢ Γᵣ {hon-≡} A →
  Action↯ {ℓ} Σ Γᵢ Γᵣ {hon-≡} B →
  Action↯ {ℓ} Σ Γᵢ Γᵣ {hon-≡} B
α >>↯ β = α >>= (λ _ → β)

S-SecureChannel : {ℓ : Level} → (M C PK L : Set ℓ) → (l : M → L) →
  (pk?= : PK → PK → Bool) → (c?= : C → C → Bool) → 
  Simulator (πᵢ-SecureChannel M L l) (πᵣ-SecureChannel M C PK L l pk?= c?=)
S-SecureChannel {ℓ} M C PK L l pk?= c?= = record
    { hon-≡     = refl
    ; state     = Lift ℓ Bool
    ; initial   = lift false
    ; call↯-map = λ
      { () here
      ; () (there here here) 
      ; _  (there here (there () _))
      ; () (there (there here) here) 
      ; _  (there (there here) (there () _))
      ; _  (there (there (there ())) _)
      }
    ; query-map = λ
      { (path here here) l → read >>= let
          perform-leak = query here (there here here) l >>= (λ c → 
            query here (there (there here) here) c)
        in λ
          -- 1. on the first leakage seen, query a π-PKE public key (ignore it).
          -- 2. on *all* leakages seen, query a π-PKE ciphertext with the leakage
          -- 3. finally, query a π-AuthChannel message, with the previous ciphertext.
          { (lift false) → query (there here) (there here here) tt >>↯ perform-leak
          ; (lift true)  → perform-leak
          }
      ; (path here (there ()))  
      ; (path (there () _) _)
      }
    }

secure : {ℓ : Level} → (M C PK L : Set ℓ) → (l : M → L) →
  (pk?= : PK → PK → Bool) → (c?= : C → C → Bool) → (m?= : M → M → Bool) →
  πᵢ-SecureChannel M L l ≃ πᵣ-SecureChannel M C PK L l pk?= c?=
secure {ℓ} M C PK L l pk?= c?= m?= = record
  { gas-map    = _* 2
  ; simulator  = S-SecureChannel M C PK L l pk?= c?=
  ; invariant  = λ
    { ⟨ ⟨ stnode (just m) [] , lift true ⟩ ,
        stnode (just pk) (
          stnode (just ⟨ pk′ , stlog ⟩) [] ∷
          stnode (just c) [] ∷
          []
        ) ⟩ → pk?= pk pk′ ∧ any (λ{ ⟨ m′ , c′ ⟩ → m?= m m′ ∧ c?= c c′ }) stlog
    ; ⟨ ⟨ stnode nothing [] , lift false ⟩ ,
        stnode nothing (
          stnode nothing [] ∷
          stnode nothing [] ∷
          []
        ) ⟩ → true
    ; _ → false
    }
  ; base-case  = refl
  ; proof      = λ
    { g σ O (call↓ here tt) ⟨
        ⟨ stnode (just m) [] , lift true ⟩ ,
        stnode (just pk′) (
          stnode (just ⟨ pk , log ⟩) [] ∷
          stnode (just c) [] ∷
          [])
      ⟩ inv → ⟨ ? , ⟨ ? , ? ⟩ ⟩ 
    ; g σ O (call↓ here tt) ⟨
        ⟨ stnode nothing [] , lift false ⟩ ,
        stnode nothing (
          stnode nothing [] ∷
          stnode nothing [] ∷
          [])
      ⟩ inv → ⟨ ? , ⟨ ? , ? ⟩ ⟩ 
    ; zero σ O (call↓ (there here) m) ⟨
        ⟨ stnode (just m′) [] , lift true ⟩ ,
        stnode (just pk′) (
          stnode (just ⟨ pk , log ⟩) [] ∷
          stnode (just c) [] ∷
          [])
      ⟩ inv → ⟨ ? , ⟨ ? , ? ⟩ ⟩ 
    ; (suc g) σ O (call↓ (there here) m) ⟨
        ⟨ stnode (just m′) [] , lift true ⟩ ,
        stnode (just pk′) (
          stnode (just ⟨ pk , log ⟩) [] ∷
          stnode (just c) [] ∷
          [])
      ⟩ inv → ⟨ ? , ⟨ ? , ? ⟩ ⟩ 
    ; g σ O (call↓ (there here) m) ⟨
        ⟨ stnode nothing [] , lift false ⟩ ,
        stnode nothing (
          stnode nothing [] ∷
          stnode nothing [] ∷
          [])
      ⟩ inv → ⟨ ? , ⟨ ? , ? ⟩ ⟩ 
    ; g σ O _ ⟨ ⟨ stnode nothing [] , lift true ⟩ , _ ⟩ inv → ⊥-elim ?
    ; g σ O _ ⟨
        ⟨ stnode _ [] , lift true ⟩ ,
        stnode nothing _
      ⟩ ()
    ; g σ O _ ⟨
        ⟨ stnode _ [] , lift true ⟩ ,
        stnode _ (stnode nothing [] ∷ _)
      ⟩ ()
    ; g σ O _ ⟨
        ⟨ stnode _ [] , lift true ⟩ ,
        stnode _ (
          stnode _ [] ∷
          stnode nothing [] ∷
          [])
      ⟩ ()
    ; g σ O _ ⟨ ⟨ stnode (just _) [] , lift false ⟩ , _ ⟩ inv → ⊥-elim ?
    ; g σ O _ ⟨
        ⟨ stnode _ [] , lift false ⟩ ,
        stnode (just _) _
      ⟩ ()
    ; g σ O _ ⟨
        ⟨ stnode _ [] , lift false ⟩ ,
        stnode _ (stnode (just _) [] ∷ _)
      ⟩ ()
    ; g σ O _ ⟨
        ⟨ stnode _ [] , lift false ⟩ ,
        stnode _ (
          stnode _ [] ∷
          stnode (just _) [] ∷
          [])
      ⟩ ()
    ; g σ O (call↓ (there (there ())) x) Σ inv
    ; g σ O (call↯ () here x) Σ inv
    ; g σ O (call↯ () (there here here) x) Σ inv
    ; g σ O (call↯ () (there (there here) here) x) Σ inv
    ; g σ O (call↯ ∈Γ (there (there (there ())) here) x) Σ inv
    ; g σ O (call↯ ∈Γ (there here (there () Γ⊑)) x) Σ inv
    ; g σ O (call↯ ∈Γ (there (there here) (there () Γ⊑)) x) Σ inv
    ; g σ O (call↯ ∈Γ (there (there (there ())) (there x₂ Γ⊑)) x) Σ inv
    }
  }
