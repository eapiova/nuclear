module Substructural.Prelude where

open import Cubical.Foundations.Prelude public hiding (_▷_)
open import Cubical.Data.Empty as Empty public using (⊥)
open import Cubical.Data.List.Base public using (List; []; _∷_; _++_; map)
open import Cubical.Data.Sigma public using (Σ; _×_; _,_; fst; snd)
open import Cubical.Data.Sum as Sum public using (_⊎_; inl; inr)
open import Cubical.Data.Unit public using (Unit; tt)

⊥-elim : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
⊥-elim = Empty.rec

inj₁ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A → A ⊎ B
inj₁ = inl

inj₂ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B → A ⊎ B
inj₂ = inr

infix 1 _↔_

record _↔_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor intro
  field
    to : A → B
    from : B → A

open _↔_ public

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
      → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘_

infixr 5 _∷ᵃ_

data All {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ-max ℓ ℓ') where
  []ᵃ : All P []
  _∷ᵃ_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

All-map
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'}
  → (∀ {x} → P x)
  → (xs : List A)
  → All P xs
All-map p [] = []ᵃ
All-map p (_ ∷ xs) = p ∷ᵃ All-map p xs

All-lookup-head
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x : A} {xs : List A}
  → All P (x ∷ xs)
  → P x
All-lookup-head (px ∷ᵃ pxs) = px

All-lookup-tail
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x : A} {xs : List A}
  → All P (x ∷ xs)
  → All P xs
All-lookup-tail (px ∷ᵃ pxs) = pxs
