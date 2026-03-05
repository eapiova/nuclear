module Substructural.FL.Lemma17 where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.FL.Basic
open import Substructural.FL.Shifts
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula
open import Cubical.Data.List.Properties using (++-unit-r)

shiftCoreInG-FLe : ∀ {j} → ShiftCoreDerivableInG j FLeRules
shiftCoreInG-FLe {j} (shift·-instance {a} {b}) []ᵃ =
  ByRule
    (inl (inl (L· {U = []} {V = []} {a = j a} {b = j b} {c = j (a `· b)})))
    (rjR· ∷ᵃ []ᵃ)
  where
  da : G⟨ j , FLeRules ⟩ (singleton (j a)) (j a)
  da = Refl

  db : G⟨ j , FLeRules ⟩ (singleton (j b)) (j b)
  db = Refl

  rjR· : G⟨ j , FLeRules ⟩ (j a ∷ j b ∷ []) (j (a `· b))
  rjR· =
    ByRule
      (inr (inr (rj-instance (inl (R· {U = singleton (j a)} {V = singleton (j b)} {a = a} {b = b})))))
      (da ∷ᵃ db ∷ᵃ []ᵃ)

shiftCoreInG-FLe {j} (shift∧-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (inl (R∧ {U = singleton (j a `∧ j b)} {a = a} {b = b})))))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
  where
  da : G⟨ j , FLeRules ⟩ (singleton (j a `∧ j b)) (j a)
  da =
    ByRule
      (inl (inl (L∧₁ {U = []} {V = []} {a = j a} {b = j b} {c = j a})))
      (Refl ∷ᵃ []ᵃ)

  db : G⟨ j , FLeRules ⟩ (singleton (j a `∧ j b)) (j b)
  db =
    ByRule
      (inl (inl (L∧₂ {U = []} {V = []} {a = j a} {b = j b} {c = j b})))
      (Refl ∷ᵃ []ᵃ)

shiftCoreInG-FLe {j} (shift⊸-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (inl (R⊸ {U = singleton (a `⊸ j b)} {a = a} {b = b})))))
    (mp ∷ᵃ []ᵃ)
  where
  mp : G⟨ j , FLeRules ⟩ (a ∷ (a `⊸ j b) ∷ []) (j b)
  mp = lift-base-into-G (mp⊸-in {R = FLeRules} {a = a} {b = j b} (inl))

shiftCoreInG-FLe {j} (shift›-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (inl (R› {U = singleton (j b `› a)} {a = a} {b = b})))))
    (mp ∷ᵃ []ᵃ)
  where
  mp : G⟨ j , FLeRules ⟩ ((j b `› a) ∷ a ∷ []) (j b)
  mp = lift-base-into-G (mp›-in {R = FLeRules} {a = a} {b = j b} (inl))

lj-ext : ∀ {j} → BiProgressiveR j FLeRules → Lj j (L⟨ ShiftCoreExt j FLeRules ⟩)
lj-ext bn = lift-BiProgressiveR bn inl

shift1∨-ext-FLe
  : ∀ {j}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → Shift1 j (L⟨ ShiftCoreExt j FLeRules ⟩)
    × Shift∨ j (L⟨ ShiftCoreExt j FLeRules ⟩)
shift1∨-ext-FLe {j} e bn = lemma16-1 (inl ∘ inl) nExt
  where
  nExt : Nucleus j (L⟨ ShiftCoreExt j FLeRules ⟩)
  nExt = mkNucleus (lift-Expansive e inl) (lift-BiProgressiveR bn inl)

survive-L⊸›-ext-FLe
  : ∀ {j}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → L⊸j-local j (L⟨ ShiftCoreExt j FLeRules ⟩)
    × L›j-local j (L⟨ ShiftCoreExt j FLeRules ⟩)
survive-L⊸›-ext-FLe {j} e bn =
  lemma16-5-proof (inl ∘ inl) (mkBiNucleus (lift-Expansive e inl) (lift-BiProgressiveR bn inl))

surv-FLe
  : ∀ {j}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → ∀ {r} → FLeRules r → SurvivesAfter j r (ShiftCoreExt j FLeRules)
surv-FLe {j} e bn (inl (L∨ {U} {V} {a} {b} {c})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∨ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
surv-FLe {j} e bn (inl (R∨₁ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j FLeRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (R∨₁ {U = U} {a = j a} {b = j b}))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-FLe {j = j} e bn) {a = a} {b = b}))
surv-FLe {j} e bn (inl (R∨₂ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j FLeRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (R∨₂ {U = U} {a = j a} {b = j b}))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-FLe {j = j} e bn) {a = a} {b = b}))
surv-FLe {j} e bn (inl (L∧₁ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∧₁ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FLe {j} e bn (inl (L∧₂ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∧₂ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FLe {j} e bn (inl (R∧ {U} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j FLeRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R∧ {U = U} {a = j a} {b = j b})))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (shift∧-instance {a = a} {b = b})) []ᵃ))
surv-FLe {j} e bn (inl (L1 {U} {V} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L1 {U = U} {V = V} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FLe {j} e bn (inl R1) []ᵃ =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (inl (inl R1)) []ᵃ)
    (fst (shift1∨-ext-FLe {j = j} e bn))
surv-FLe {j} e bn (inl (L· {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L· {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FLe {j} e bn (inl (R· {U} {V} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j FLeRules)} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R· {U = U} {V = V} {a = j a} {b = j b})))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (shift·-instance {a = a} {b = b})) []ᵃ))
surv-FLe {j} e bn (inl (L⊸ {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  fst (survive-L⊸›-ext-FLe {j = j} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FLe {j} e bn (inl (R⊸ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j FLeRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R⊸ {U = U} {a = a} {b = j b})))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (shift⊸-instance {a = a} {b = b})) []ᵃ))
surv-FLe {j} e bn (inl (L› {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  snd (survive-L⊸›-ext-FLe {j = j} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FLe {j} e bn (inl (R› {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j FLeRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R› {U = U} {a = a} {b = j b})))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (shift›-instance {a = a} {b = b})) []ᵃ))
surv-FLe {j} e bn (inr (comm-instance {U₁} {U₂} {a₁} {a₂} {b})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inr (comm-instance {U₁ = U₁} {U₂ = U₂} {a₁ = a₁} {a₂ = a₂} {b = j b})))
    (d ∷ᵃ []ᵃ)

lemma17-FLe
  : ∀ {j}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → (G⟨ j , FLeRules ⟩ ⊆ L⟨ ShiftCoreExt j FLeRules ⟩)
    × (L⟨ ShiftCoreExt j FLeRules ⟩ ⊆ G⟨ j , FLeRules ⟩)
lemma17-FLe e bn = lemma17-proof (lj-ext bn) (surv-FLe e bn) shiftCoreInG-FLe
