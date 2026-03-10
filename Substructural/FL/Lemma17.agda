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
shift1∨-ext-FLe {j} e bn = lemma1-1 (inl ∘ inl) nExt
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
  lemma1-5-proof (inl ∘ inl) (mkBiNucleus (lift-Expansive e inl) (lift-BiProgressiveR bn inl))

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

lemma2-FLe
  : ∀ {j}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → (G⟨ j , FLeRules ⟩ ⊆ L⟨ ShiftCoreExt j FLeRules ⟩)
    × (L⟨ ShiftCoreExt j FLeRules ⟩ ⊆ G⟨ j , FLeRules ⟩)
lemma2-FLe e bn = lemma2-proof (lj-ext bn) (surv-FLe e bn) shiftCoreInG-FLe

-- Generalized versions for L = FLe + R₂

shiftCoreInG-FLe-gen : ∀ {j R₂} → ShiftCoreDerivableInG j (FLeRules ∪R R₂)
shiftCoreInG-FLe-gen sr []ᵃ = lift-G inl (shiftCoreInG-FLe sr []ᵃ)

lj-ext-FLe-gen : ∀ {j R₂} → BiProgressiveR j FLeRules → Lj j (L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩)
lj-ext-FLe-gen bn = lift-BiProgressiveR bn (inl ∘ inl)

shift1∨-ext-FLe-gen
  : ∀ {j R₂}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → Shift1 j (L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩)
    × Shift∨ j (L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩)
shift1∨-ext-FLe-gen {j} e bn = lemma1-1 (inl ∘ inl ∘ inl) nExt
  where
  nExt : Nucleus j (L⟨ ShiftCoreExtGen j FLeRules _ ⟩)
  nExt = mkNucleus (lift-Expansive e (inl ∘ inl)) (lift-BiProgressiveR bn (inl ∘ inl))

survive-L⊸›-ext-FLe-gen
  : ∀ {j R₂}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → L⊸j-local j (L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩)
    × L›j-local j (L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩)
survive-L⊸›-ext-FLe-gen {j} e bn =
  lemma1-5-proof (inl ∘ inl ∘ inl) (mkBiNucleus (lift-Expansive e (inl ∘ inl)) (lift-BiProgressiveR bn (inl ∘ inl)))

surv-FLe-gen
  : ∀ {j R₂}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → ∀ {r} → FLeRules r → SurvivesAfter j r (ShiftCoreExtGen j FLeRules R₂)
surv-FLe-gen {j} {R₂} e bn (inl (L∨ {U} {V} {a} {b} {c})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L∨ {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
surv-FLe-gen {j} {R₂} e bn (inl (R∨₁ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j FLeRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (inl (R∨₁ {U = U} {a = j a} {b = j b})))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-FLe-gen {j = j} {R₂ = R₂} e bn) {a = a} {b = b}))
surv-FLe-gen {j} {R₂} e bn (inl (R∨₂ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j FLeRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (inl (R∨₂ {U = U} {a = j a} {b = j b})))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-FLe-gen {j = j} {R₂ = R₂} e bn) {a = a} {b = b}))
surv-FLe-gen {j} {R₂} e bn (inl (L∧₁ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L∧₁ {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-FLe-gen {j} {R₂} e bn (inl (L∧₂ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L∧₂ {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-FLe-gen {j} {R₂} e bn (inl (R∧ {U} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j FLeRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R∧ {U = U} {a = j a} {b = j b}))))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift∧-instance {a = a} {b = b}))) []ᵃ))
surv-FLe-gen {j} {R₂} e bn (inl (L1 {U} {V} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L1 {U = U} {V = V} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-FLe-gen {j} {R₂} e bn (inl R1) []ᵃ =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (inl (inl (inl R1))) []ᵃ)
    (fst (shift1∨-ext-FLe-gen {j = j} {R₂ = R₂} e bn))
surv-FLe-gen {j} {R₂} e bn (inl (L· {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L· {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-FLe-gen {j} {R₂} e bn (inl (R· {U} {V} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j FLeRules R₂)} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R· {U = U} {V = V} {a = j a} {b = j b}))))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift·-instance {a = a} {b = b}))) []ᵃ))
surv-FLe-gen {j} {R₂} e bn (inl (L⊸ {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  fst (survive-L⊸›-ext-FLe-gen {j = j} {R₂ = R₂} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FLe-gen {j} {R₂} e bn (inl (R⊸ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j FLeRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R⊸ {U = U} {a = a} {b = j b}))))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift⊸-instance {a = a} {b = b}))) []ᵃ))
surv-FLe-gen {j} {R₂} e bn (inl (L› {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  snd (survive-L⊸›-ext-FLe-gen {j = j} {R₂ = R₂} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FLe-gen {j} {R₂} e bn (inl (R› {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j FLeRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R› {U = U} {a = a} {b = j b}))))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift›-instance {a = a} {b = b}))) []ᵃ))
surv-FLe-gen {j} {R₂} e bn (inr (comm-instance {U₁} {U₂} {a₁} {a₂} {b})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inr (comm-instance {U₁ = U₁} {U₂ = U₂} {a₁ = a₁} {a₂ = a₂} {b = j b}))))
    (d ∷ᵃ []ᵃ)

lemma2-FLe-gen
  : ∀ {j R₂}
  → Expansive j FLeRules
  → BiProgressiveR j FLeRules
  → (G⟨ j , FLeRules ∪R R₂ ⟩ ⊆ L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩)
    × (L⟨ ShiftCoreExtGen j FLeRules R₂ ⟩ ⊆ G⟨ j , FLeRules ∪R R₂ ⟩)
lemma2-FLe-gen e bn = lemma2-proof-gen (lj-ext-FLe-gen bn) (surv-FLe-gen e bn) shiftCoreInG-FLe-gen

shiftCoreInG-FL : ∀ {j} → ShiftCoreDerivableInG j FLRules
shiftCoreInG-FL {j} (shift·-instance {a} {b}) []ᵃ =
  ByRule
    (inl (L· {U = []} {V = []} {a = j a} {b = j b} {c = j (a `· b)}))
    (rjR· ∷ᵃ []ᵃ)
  where
  da : G⟨ j , FLRules ⟩ (singleton (j a)) (j a)
  da = Refl

  db : G⟨ j , FLRules ⟩ (singleton (j b)) (j b)
  db = Refl

  rjR· : G⟨ j , FLRules ⟩ (j a ∷ j b ∷ []) (j (a `· b))
  rjR· =
    ByRule
      (inr (inr (rj-instance (R· {U = singleton (j a)} {V = singleton (j b)} {a = a} {b = b}))))
      (da ∷ᵃ db ∷ᵃ []ᵃ)

shiftCoreInG-FL {j} (shift∧-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (R∧ {U = singleton (j a `∧ j b)} {a = a} {b = b}))))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
  where
  da : G⟨ j , FLRules ⟩ (singleton (j a `∧ j b)) (j a)
  da =
    ByRule
      (inl (L∧₁ {U = []} {V = []} {a = j a} {b = j b} {c = j a}))
      (Refl ∷ᵃ []ᵃ)

  db : G⟨ j , FLRules ⟩ (singleton (j a `∧ j b)) (j b)
  db =
    ByRule
      (inl (L∧₂ {U = []} {V = []} {a = j a} {b = j b} {c = j b}))
      (Refl ∷ᵃ []ᵃ)

shiftCoreInG-FL {j} (shift⊸-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (R⊸ {U = singleton (a `⊸ j b)} {a = a} {b = b}))))
    (mp ∷ᵃ []ᵃ)
  where
  mp : G⟨ j , FLRules ⟩ (a ∷ (a `⊸ j b) ∷ []) (j b)
  mp = mp⊸-in {R = GjRules j FLRules} {a = a} {b = j b} inl

shiftCoreInG-FL {j} (shift›-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (R› {U = singleton (j b `› a)} {a = a} {b = b}))))
    (mp ∷ᵃ []ᵃ)
  where
  mp : G⟨ j , FLRules ⟩ ((j b `› a) ∷ a ∷ []) (j b)
  mp = mp›-in {R = GjRules j FLRules} {a = a} {b = j b} inl

shift·-in-ext : ∀ {j} → Shift· j (L⟨ ShiftCoreExt j FLRules ⟩)
shift·-in-ext = ByRule (inr shift·-instance) []ᵃ

lj-ext-FL
  : ∀ {j}
  → Expansive j FLRules
  → LeftProgressiveR j FLRules ⊎ (RightProgressiveR j FLRules ⊎ BiProgressiveR j FLRules)
  → Lj j (L⟨ ShiftCoreExt j FLRules ⟩)
lj-ext-FL e (inl lpn) =
  ljleft+shift·→lj inl
    (lift-Expansive e inl)
    (lift-LeftProgressiveR lpn inl)
    shift·-in-ext
lj-ext-FL e (inr (inl rpn)) =
  ljright+shift·→lj inl
    (lift-Expansive e inl)
    (lift-RightProgressiveR rpn inl)
    shift·-in-ext
lj-ext-FL e (inr (inr bn)) =
  lift-BiProgressiveR bn inl

survive-L⊸›-ext-FL
  : ∀ {j}
  → Expansive j FLRules
  → Lj j (L⟨ ShiftCoreExt j FLRules ⟩)
  → L⊸j-local j (L⟨ ShiftCoreExt j FLRules ⟩)
    × L›j-local j (L⟨ ShiftCoreExt j FLRules ⟩)
survive-L⊸›-ext-FL {j} e lj =
  lemma1-5-proof inl (mkBiNucleus (lift-Expansive e inl) lj)

surv-FL
  : ∀ {j}
  → Expansive j FLRules
  → Lj j (L⟨ ShiftCoreExt j FLRules ⟩)
  → ∀ {r} → FLRules r → SurvivesAfter j r (ShiftCoreExt j FLRules)
surv-FL {j} e lj (L∨ {U} {V} {a} {b} {c}) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  ByRule
    (inl (L∨ {U = U} {V = V} {a = a} {b = b} {c = j c}))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
surv-FL {j} e lj (R∨₁ {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (R∨₁ {U = U} {a = j a} {b = j b})) (d ∷ᵃ []ᵃ))
      (snd (lemma1-1 inl (mkNucleus (lift-Expansive e inl) lj)) {a = a} {b = b}))
surv-FL {j} e lj (R∨₂ {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (R∨₂ {U = U} {a = j a} {b = j b})) (d ∷ᵃ []ᵃ))
      (snd (lemma1-1 inl (mkNucleus (lift-Expansive e inl) lj)) {a = a} {b = b}))
surv-FL {j} e lj (L∧₁ {U} {V} {a} {b} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (L∧₁ {U = U} {V = V} {a = a} {b = b} {c = j c}))
    (d ∷ᵃ []ᵃ)
surv-FL {j} e lj (L∧₂ {U} {V} {a} {b} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (L∧₂ {U = U} {V = V} {a = a} {b = b} {c = j c}))
    (d ∷ᵃ []ᵃ)
surv-FL {j} e lj (R∧ {U} {a} {b}) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (R∧ {U = U} {a = j a} {b = j b}))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (shift∧-instance {a = a} {b = b})) []ᵃ))
surv-FL {j} e lj (L1 {U} {V} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (L1 {U = U} {V = V} {c = j c}))
    (d ∷ᵃ []ᵃ)
surv-FL {j} e lj R1 []ᵃ =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (inl R1) []ᵃ)
    (fst (lemma1-1 inl (mkNucleus (lift-Expansive e inl) lj)))
surv-FL {j} e lj (L· {U} {V} {a} {b} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (L· {U = U} {V = V} {a = a} {b = b} {c = j c}))
    (d ∷ᵃ []ᵃ)
surv-FL {j} e lj (R· {U} {V} {a} {b}) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (R· {U = U} {V = V} {a = j a} {b = j b}))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (shift·-instance {a = a} {b = b})) []ᵃ))
surv-FL {j} e lj (L⊸ {U} {V} {W} {a} {b} {c}) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  fst (survive-L⊸›-ext-FL {j = j} e lj)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FL {j} e lj (R⊸ {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (R⊸ {U = U} {a = a} {b = j b}))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (shift⊸-instance {a = a} {b = b})) []ᵃ))
surv-FL {j} e lj (L› {U} {V} {W} {a} {b} {c}) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  snd (survive-L⊸›-ext-FL {j = j} e lj)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FL {j} e lj (R› {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (R› {U = U} {a = a} {b = j b}))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (shift›-instance {a = a} {b = b})) []ᵃ))

lemma2-FL
  : ∀ {j}
  → Expansive j FLRules
  → LeftProgressiveR j FLRules ⊎ (RightProgressiveR j FLRules ⊎ BiProgressiveR j FLRules)
  → (G⟨ j , FLRules ⟩ ⊆ L⟨ ShiftCoreExt j FLRules ⟩)
    × (L⟨ ShiftCoreExt j FLRules ⟩ ⊆ G⟨ j , FLRules ⟩)
lemma2-FL e pn =
  lemma2-proof (lj-ext-FL e pn) (surv-FL e (lj-ext-FL e pn)) shiftCoreInG-FL

-- Generalized versions for L = FL + R₂

shiftCoreInG-FL-gen : ∀ {j R₂} → ShiftCoreDerivableInG j (FLRules ∪R R₂)
shiftCoreInG-FL-gen sr []ᵃ = lift-G inl (shiftCoreInG-FL sr []ᵃ)

shift·-in-ext-gen-FL : ∀ {j R₂} → Shift· j (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
shift·-in-ext-gen-FL = ByRule (inr (inl shift·-instance)) []ᵃ

lj-ext-FL-gen
  : ∀ {j R₂}
  → Expansive j FLRules
  → LeftProgressiveR j FLRules ⊎ (RightProgressiveR j FLRules ⊎ BiProgressiveR j FLRules)
  → Lj j (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
lj-ext-FL-gen e (inl lpn) =
  ljleft+shift·→lj (inl ∘ inl)
    (lift-Expansive e (inl ∘ inl))
    (lift-LeftProgressiveR lpn (inl ∘ inl))
    shift·-in-ext-gen-FL
lj-ext-FL-gen e (inr (inl rpn)) =
  ljright+shift·→lj (inl ∘ inl)
    (lift-Expansive e (inl ∘ inl))
    (lift-RightProgressiveR rpn (inl ∘ inl))
    shift·-in-ext-gen-FL
lj-ext-FL-gen e (inr (inr bn)) =
  lift-BiProgressiveR bn (inl ∘ inl)

survive-L⊸›-ext-FL-gen
  : ∀ {j R₂}
  → Expansive j FLRules
  → Lj j (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
  → L⊸j-local j (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
    × L›j-local j (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
survive-L⊸›-ext-FL-gen {j} {R₂} e lj =
  lemma1-5-proof (inl ∘ inl) (mkBiNucleus (lift-Expansive e (inl ∘ inl)) lj)

surv-FL-gen
  : ∀ {j R₂}
  → Expansive j FLRules
  → Lj j (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
  → ∀ {r} → FLRules r → SurvivesAfter j r (ShiftCoreExtGen j FLRules R₂)
surv-FL-gen {j} {R₂} e lj (L∨ {U} {V} {a} {b} {c}) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∨ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
surv-FL-gen {j} {R₂} e lj (R∨₁ {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (R∨₁ {U = U} {a = j a} {b = j b}))) (d ∷ᵃ []ᵃ))
      (snd (lemma1-1 (inl ∘ inl) (mkNucleus (lift-Expansive e (inl ∘ inl)) lj)) {a = a} {b = b}))
surv-FL-gen {j} {R₂} e lj (R∨₂ {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (R∨₂ {U = U} {a = j a} {b = j b}))) (d ∷ᵃ []ᵃ))
      (snd (lemma1-1 (inl ∘ inl) (mkNucleus (lift-Expansive e (inl ∘ inl)) lj)) {a = a} {b = b}))
surv-FL-gen {j} {R₂} e lj (L∧₁ {U} {V} {a} {b} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∧₁ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FL-gen {j} {R₂} e lj (L∧₂ {U} {V} {a} {b} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∧₂ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FL-gen {j} {R₂} e lj (R∧ {U} {a} {b}) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R∧ {U = U} {a = j a} {b = j b})))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift∧-instance {a = a} {b = b}))) []ᵃ))
surv-FL-gen {j} {R₂} e lj (L1 {U} {V} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L1 {U = U} {V = V} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FL-gen {j} {R₂} e lj R1 []ᵃ =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (inl (inl R1)) []ᵃ)
    (fst (lemma1-1 (inl ∘ inl) (mkNucleus (lift-Expansive e (inl ∘ inl)) lj)))
surv-FL-gen {j} {R₂} e lj (L· {U} {V} {a} {b} {c}) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L· {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-FL-gen {j} {R₂} e lj (R· {U} {V} {a} {b}) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R· {U = U} {V = V} {a = j a} {b = j b})))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift·-instance {a = a} {b = b}))) []ᵃ))
surv-FL-gen {j} {R₂} e lj (L⊸ {U} {V} {W} {a} {b} {c}) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  fst (survive-L⊸›-ext-FL-gen {j = j} {R₂ = R₂} e lj)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FL-gen {j} {R₂} e lj (R⊸ {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R⊸ {U = U} {a = a} {b = j b})))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift⊸-instance {a = a} {b = b}))) []ᵃ))
surv-FL-gen {j} {R₂} e lj (L› {U} {V} {W} {a} {b} {c}) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  snd (survive-L⊸›-ext-FL-gen {j = j} {R₂ = R₂} e lj)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-FL-gen {j} {R₂} e lj (R› {U} {a} {b}) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv _} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R› {U = U} {a = a} {b = j b})))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift›-instance {a = a} {b = b}))) []ᵃ))

lemma2-FL-gen
  : ∀ {j R₂}
  → Expansive j FLRules
  → LeftProgressiveR j FLRules ⊎ (RightProgressiveR j FLRules ⊎ BiProgressiveR j FLRules)
  → (G⟨ j , FLRules ∪R R₂ ⟩ ⊆ L⟨ ShiftCoreExtGen j FLRules R₂ ⟩)
    × (L⟨ ShiftCoreExtGen j FLRules R₂ ⟩ ⊆ G⟨ j , FLRules ∪R R₂ ⟩)
lemma2-FL-gen e pn =
  lemma2-proof-gen (lj-ext-FL-gen e pn) (surv-FL-gen e (lj-ext-FL-gen e pn)) shiftCoreInG-FL-gen

shiftCoreInG-Min : ∀ {j} → ShiftCoreDerivableInG j MinRules
shiftCoreInG-Min {j} (shift·-instance {a} {b}) []ᵃ =
  ByRule
    (inl (inl (L· {U = []} {V = []} {a = j a} {b = j b} {c = j (a `· b)})))
    (rjR· ∷ᵃ []ᵃ)
  where
  rjR· : G⟨ j , MinRules ⟩ (j a ∷ j b ∷ []) (j (a `· b))
  rjR· =
    ByRule
      (inr (inr (rj-instance (inl (R· {U = singleton (j a)} {V = singleton (j b)} {a = a} {b = b})))))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)
shiftCoreInG-Min {j} (shift∧-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (inl (R∧ {U = singleton (j a `∧ j b)} {a = a} {b = b})))))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
  where
  da : G⟨ j , MinRules ⟩ (singleton (j a `∧ j b)) (j a)
  da =
    ByRule
      (inl (inl (L∧₁ {U = []} {V = []} {a = j a} {b = j b} {c = j a})))
      (Refl ∷ᵃ []ᵃ)
  db : G⟨ j , MinRules ⟩ (singleton (j a `∧ j b)) (j b)
  db =
    ByRule
      (inl (inl (L∧₂ {U = []} {V = []} {a = j a} {b = j b} {c = j b})))
      (Refl ∷ᵃ []ᵃ)
shiftCoreInG-Min {j} (shift⊸-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (inl (R⊸ {U = singleton (a `⊸ j b)} {a = a} {b = b})))))
    (mp ∷ᵃ []ᵃ)
  where
  mp : G⟨ j , MinRules ⟩ (a ∷ (a `⊸ j b) ∷ []) (j b)
  mp = lift-base-into-G (mp⊸-in {R = MinRules} {a = a} {b = j b} inl)
shiftCoreInG-Min {j} (shift›-instance {a} {b}) []ᵃ =
  ByRule
    (inr (inr (rj-instance (inl (R› {U = singleton (j b `› a)} {a = a} {b = b})))))
    (mp ∷ᵃ []ᵃ)
  where
  mp : G⟨ j , MinRules ⟩ ((j b `› a) ∷ a ∷ []) (j b)
  mp = lift-base-into-G (mp›-in {R = MinRules} {a = a} {b = j b} inl)

lj-ext-Min : ∀ {j} → BiProgressiveR j MinRules → Lj j (L⟨ ShiftCoreExt j MinRules ⟩)
lj-ext-Min bn = lift-BiProgressiveR bn inl

shift1∨-ext-Min
  : ∀ {j}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → Shift1 j (L⟨ ShiftCoreExt j MinRules ⟩)
    × Shift∨ j (L⟨ ShiftCoreExt j MinRules ⟩)
shift1∨-ext-Min {j} e bn = lemma1-1 (inl ∘ inl) nExt
  where
  nExt : Nucleus j (L⟨ ShiftCoreExt j MinRules ⟩)
  nExt = mkNucleus (lift-Expansive e inl) (lift-BiProgressiveR bn inl)

survive-L⊸›-ext-Min
  : ∀ {j}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → L⊸j-local j (L⟨ ShiftCoreExt j MinRules ⟩)
    × L›j-local j (L⟨ ShiftCoreExt j MinRules ⟩)
survive-L⊸›-ext-Min {j} e bn =
  lemma1-5-proof (inl ∘ inl) (mkBiNucleus (lift-Expansive e inl) (lift-BiProgressiveR bn inl))

surv-Min
  : ∀ {j}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → ∀ {r} → MinRules r → SurvivesAfter j r (ShiftCoreExt j MinRules)
-- FL rules (same structure as surv-FLe)
surv-Min {j} e bn (inl (L∨ {U} {V} {a} {b} {c})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∨ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
surv-Min {j} e bn (inl (R∨₁ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j MinRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (R∨₁ {U = U} {a = j a} {b = j b}))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-Min {j = j} e bn) {a = a} {b = b}))
surv-Min {j} e bn (inl (R∨₂ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j MinRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (R∨₂ {U = U} {a = j a} {b = j b}))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-Min {j = j} e bn) {a = a} {b = b}))
surv-Min {j} e bn (inl (L∧₁ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∧₁ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-Min {j} e bn (inl (L∧₂ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L∧₂ {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-Min {j} e bn (inl (R∧ {U} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j MinRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R∧ {U = U} {a = j a} {b = j b})))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (shift∧-instance {a = a} {b = b})) []ᵃ))
surv-Min {j} e bn (inl (L1 {U} {V} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L1 {U = U} {V = V} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-Min {j} e bn (inl R1) []ᵃ =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (inl (inl R1)) []ᵃ)
    (fst (shift1∨-ext-Min {j = j} e bn))
surv-Min {j} e bn (inl (L· {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (L· {U = U} {V = V} {a = a} {b = b} {c = j c})))
    (d ∷ᵃ []ᵃ)
surv-Min {j} e bn (inl (R· {U} {V} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j MinRules)} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R· {U = U} {V = V} {a = j a} {b = j b})))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (shift·-instance {a = a} {b = b})) []ᵃ))
surv-Min {j} e bn (inl (L⊸ {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  fst (survive-L⊸›-ext-Min {j = j} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-Min {j} e bn (inl (R⊸ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j MinRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R⊸ {U = U} {a = a} {b = j b})))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (shift⊸-instance {a = a} {b = b})) []ᵃ))
surv-Min {j} e bn (inl (L› {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  snd (survive-L⊸›-ext-Min {j = j} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-Min {j} e bn (inl (R› {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExt j MinRules)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (R› {U = U} {a = a} {b = j b})))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (shift›-instance {a = a} {b = b})) []ᵃ))
-- Structural rules
surv-Min {j} e bn (inr (inl (comm-instance {U₁} {U₂} {a₁} {a₂} {b}))) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inr (inl (comm-instance {U₁ = U₁} {U₂ = U₂} {a₁ = a₁} {a₂ = a₂} {b = j b}))))
    (d ∷ᵃ []ᵃ)
surv-Min {j} e bn (inr (inr (inl (mono-instance {U₁} {U₂} {a} {b})))) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inr (inr (inl (mono-instance {U₁ = U₁} {U₂ = U₂} {a = a} {b = j b})))))
    (d ∷ᵃ []ᵃ)
surv-Min {j} e bn (inr (inr (inr (contr-instance {U₁} {U₂} {a} {b})))) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inr (inr (inr (contr-instance {U₁ = U₁} {U₂ = U₂} {a = a} {b = j b})))))
    (d ∷ᵃ []ᵃ)

lemma2-Min
  : ∀ {j}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → (G⟨ j , MinRules ⟩ ⊆ L⟨ ShiftCoreExt j MinRules ⟩)
    × (L⟨ ShiftCoreExt j MinRules ⟩ ⊆ G⟨ j , MinRules ⟩)
lemma2-Min e bn = lemma2-proof (lj-ext-Min bn) (surv-Min e bn) shiftCoreInG-Min

-- Generalized versions for L = Min + R₂

shiftCoreInG-Min-gen : ∀ {j R₂} → ShiftCoreDerivableInG j (MinRules ∪R R₂)
shiftCoreInG-Min-gen sr []ᵃ = lift-G inl (shiftCoreInG-Min sr []ᵃ)

lj-ext-Min-gen : ∀ {j R₂} → BiProgressiveR j MinRules → Lj j (L⟨ ShiftCoreExtGen j MinRules R₂ ⟩)
lj-ext-Min-gen bn = lift-BiProgressiveR bn (inl ∘ inl)

shift1∨-ext-Min-gen
  : ∀ {j R₂}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → Shift1 j (L⟨ ShiftCoreExtGen j MinRules R₂ ⟩)
    × Shift∨ j (L⟨ ShiftCoreExtGen j MinRules R₂ ⟩)
shift1∨-ext-Min-gen {j} e bn = lemma1-1 (inl ∘ inl ∘ inl) nExt
  where
  nExt : Nucleus j (L⟨ ShiftCoreExtGen j MinRules _ ⟩)
  nExt = mkNucleus (lift-Expansive e (inl ∘ inl)) (lift-BiProgressiveR bn (inl ∘ inl))

survive-L⊸›-ext-Min-gen
  : ∀ {j R₂}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → L⊸j-local j (L⟨ ShiftCoreExtGen j MinRules R₂ ⟩)
    × L›j-local j (L⟨ ShiftCoreExtGen j MinRules R₂ ⟩)
survive-L⊸›-ext-Min-gen {j} e bn =
  lemma1-5-proof (inl ∘ inl ∘ inl) (mkBiNucleus (lift-Expansive e (inl ∘ inl)) (lift-BiProgressiveR bn (inl ∘ inl)))

surv-Min-gen
  : ∀ {j R₂}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → ∀ {r} → MinRules r → SurvivesAfter j r (ShiftCoreExtGen j MinRules R₂)
-- FL rules
surv-Min-gen {j} {R₂} e bn (inl (L∨ {U} {V} {a} {b} {c})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L∨ {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inl (R∨₁ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j MinRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (inl (R∨₁ {U = U} {a = j a} {b = j b})))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-Min-gen {j = j} {R₂ = R₂} e bn) {a = a} {b = b}))
surv-Min-gen {j} {R₂} e bn (inl (R∨₂ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j MinRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (inl (inl (inl (R∨₂ {U = U} {a = j a} {b = j b})))) (d ∷ᵃ []ᵃ))
      (snd (shift1∨-ext-Min-gen {j = j} {R₂ = R₂} e bn) {a = a} {b = b}))
surv-Min-gen {j} {R₂} e bn (inl (L∧₁ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L∧₁ {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inl (L∧₂ {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L∧₂ {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inl (R∧ {U} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j MinRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R∧ {U = U} {a = j a} {b = j b}))))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift∧-instance {a = a} {b = b}))) []ᵃ))
surv-Min-gen {j} {R₂} e bn (inl (L1 {U} {V} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L1 {U = U} {V = V} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inl R1) []ᵃ =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (inl (inl (inl R1))) []ᵃ)
    (fst (shift1∨-ext-Min-gen {j = j} {R₂ = R₂} e bn))
surv-Min-gen {j} {R₂} e bn (inl (L· {U} {V} {a} {b} {c})) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inl (L· {U = U} {V = V} {a = a} {b = b} {c = j c}))))
    (d ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inl (R· {U} {V} {a} {b})) (da ∷ᵃ db ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j MinRules R₂)} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R· {U = U} {V = V} {a = j a} {b = j b}))))
        (da ∷ᵃ db ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift·-instance {a = a} {b = b}))) []ᵃ))
surv-Min-gen {j} {R₂} e bn (inl (L⊸ {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  fst (survive-L⊸›-ext-Min-gen {j = j} {R₂ = R₂} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-Min-gen {j} {R₂} e bn (inl (R⊸ {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j MinRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R⊸ {U = U} {a = a} {b = j b}))))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift⊸-instance {a = a} {b = b}))) []ᵃ))
surv-Min-gen {j} {R₂} e bn (inl (L› {U} {V} {W} {a} {b} {c})) (dU ∷ᵃ dWV ∷ᵃ []ᵃ) =
  snd (survive-L⊸›-ext-Min-gen {j = j} {R₂ = R₂} e bn)
    {U = U} {V = V} {W = W} {a = a} {b = b} {c = c} dU dWV
surv-Min-gen {j} {R₂} e bn (inl (R› {U} {a} {b})) (d ∷ᵃ []ᵃ) =
  transportCtx {L = Deriv (ShiftCoreExtGen j MinRules R₂)} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule
        (inl (inl (inl (R› {U = U} {a = a} {b = j b}))))
        (d ∷ᵃ []ᵃ))
      (ByRule (inr (inl (shift›-instance {a = a} {b = b}))) []ᵃ))
-- Structural rules
surv-Min-gen {j} {R₂} e bn (inr (inl (comm-instance {U₁} {U₂} {a₁} {a₂} {b}))) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inr (inl (comm-instance {U₁ = U₁} {U₂ = U₂} {a₁ = a₁} {a₂ = a₂} {b = j b})))))
    (d ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inr (inr (inl (mono-instance {U₁} {U₂} {a} {b})))) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inr (inr (inl (mono-instance {U₁ = U₁} {U₂ = U₂} {a = a} {b = j b}))))))
    (d ∷ᵃ []ᵃ)
surv-Min-gen {j} {R₂} e bn (inr (inr (inr (contr-instance {U₁} {U₂} {a} {b})))) (d ∷ᵃ []ᵃ) =
  ByRule
    (inl (inl (inr (inr (inr (contr-instance {U₁ = U₁} {U₂ = U₂} {a = a} {b = j b}))))))
    (d ∷ᵃ []ᵃ)

lemma2-Min-gen
  : ∀ {j R₂}
  → Expansive j MinRules
  → BiProgressiveR j MinRules
  → (G⟨ j , MinRules ∪R R₂ ⟩ ⊆ L⟨ ShiftCoreExtGen j MinRules R₂ ⟩)
    × (L⟨ ShiftCoreExtGen j MinRules R₂ ⟩ ⊆ G⟨ j , MinRules ∪R R₂ ⟩)
lemma2-Min-gen e bn = lemma2-proof-gen (lj-ext-Min-gen bn) (surv-Min-gen e bn) shiftCoreInG-Min-gen
