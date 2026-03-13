open import Cubical.Core.Primitives

module Substructural.Core.Judgement {ℓ} (S : Type ℓ) where

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

mapSucc : (S → S) → Seq → Seq
mapSucc j (Γ ▷ a) = Γ ▷ j a

mapCtx : (S → S) → Ctx → Ctx
mapCtx f = map f

mapBoth : (S → S) → Seq → Seq
mapBoth f (Γ ▷ a) = mapCtx f Γ ▷ f a

mapCtx-++ : (f : S → S) → (U V : Ctx) → mapCtx f (U ++ V) ≡ mapCtx f U ++ mapCtx f V
mapCtx-++ f U V = sym (map++ f U V)
