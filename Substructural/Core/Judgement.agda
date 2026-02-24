{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Judgement {ℓ} (S : Set ℓ) where

open import Substructural.Prelude
open import Cubical.Data.List.Properties using (map++)

-- Glivenko_substructural.pdf, Section 2:
-- contexts are finite lists over the object language S.
Ctx : Type ℓ
Ctx = List S

infix 3 _▷_

record Seq : Type ℓ where
  constructor _▷_
  field
    ctx : Ctx
    obj : S

open Seq public

singleton : S → Ctx
singleton a = a ∷ []

-- Context plugging used by the paper's Trans rule:
-- from U ▷ a and V₁ , a , V₂ ▷ b derive V₁ , U , V₂ ▷ b.
plug : Ctx → Ctx → Ctx → Ctx
plug U V W = U ++ W ++ V

plug₁ : Ctx → S → Ctx → Ctx
plug₁ U a V = U ++ (a ∷ V)

mapSucc : (S → S) → Seq → Seq
mapSucc j (Γ ▷ a) = Γ ▷ j a

mapCtx : (S → S) → Ctx → Ctx
mapCtx f = map f

mapBoth : (S → S) → Seq → Seq
mapBoth f (Γ ▷ a) = mapCtx f Γ ▷ f a

mapCtx-++ : (f : S → S) → (U V : Ctx) → mapCtx f (U ++ V) ≡ mapCtx f U ++ mapCtx f V
mapCtx-++ f U V = sym (map++ f U V)

mapCtx-plug₁
  : (f : S → S)
  → (U : Ctx) (a : S) (V : Ctx)
  → mapCtx f (plug₁ U a V) ≡ plug₁ (mapCtx f U) (f a) (mapCtx f V)
mapCtx-plug₁ f U a V = sym (map++ f U (a ∷ V))

mapCtx-plug
  : (f : S → S)
  → (U V W : Ctx)
  → mapCtx f (plug U V W) ≡ plug (mapCtx f U) (mapCtx f V) (mapCtx f W)
mapCtx-plug f U V W =
  sym (map++ f U (W ++ V))
  ∙ cong (λ X → mapCtx f U ++ X) (sym (map++ f W V))
