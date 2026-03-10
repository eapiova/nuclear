module Substructural.FL.Theorem19 where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.FL.Basic
open import Substructural.FL.Shifts
open import Substructural.FL.Lemma17
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula
open import Cubical.Data.List.Properties using (++-unit-r)

private
  variable
    j : Formula → Formula
    R : RuleSet
    Γ : Ctx
    a b : Formula

cond2→cond1
  : ∀ {j R}
  → Expansive j FLRules
  → Deriv R ⊆ M⟨ j , FLRules ⟩
  → Theorem3-Cond2 j (Deriv R)
  → Theorem3-Cond1 j (Deriv R)
cond2→cond1 {j} {R} e l⊆m g⊆l {Γ} {a} =
  intro to' from'
  where
  to'
    : M⟨ j , FLRules ⟩ Γ a
    → Deriv R Γ (j a)
  to' d = g⊆l (m→gj e d)

  from'
    : Deriv R Γ (j a)
    → M⟨ j , FLRules ⟩ Γ a
  from' d = destab-M (l⊆m d)

cond1→cond2
  : ∀ {j R}
  → FLRules ⊆R R
  → Expansive j FLRules
  → Theorem3-Cond1 j (Deriv R)
  → Theorem3-Cond2 j (Deriv R)
cond1→cond2 {j} {R} iFL e c1 = g→l
  where
  m⊆k : M⟨ j , FLRules ⟩ ⊆ Kj j (Deriv R)
  m⊆k {Γ} {a} d = to (c1 {Γ = Γ} {a = a}) d

  g⊆k : G⟨ j , FLRules ⟩ ⊆ Kj j (Deriv R)
  g⊆k d = m⊆k (g⊆m e d)

  jj→j : ∀ b → Deriv R (singleton (j (j b))) (j b)
  jj→j b = m⊆k d
    where
    lj+M : Lj+ j (M⟨ j , FLRules ⟩)
    lj+M = jstab→lj+ (λ a → jstab-in-M {j = j} {R = FLRules} {a = a})

    d : M⟨ j , FLRules ⟩ (singleton (j (j b))) b
    d = lj+M {U = []} {V = []} {a = j b} {b = b} jstab-in-M

  mutual

    g→l-all
      : ∀ {ps}
      → PremisesHold (G⟨ j , FLRules ⟩) ps
      → PremisesHold (Deriv R) ps
    g→l-all {ps = []} []ᵃ = []ᵃ
    g→l-all {ps = p ∷ ps} (d ∷ᵃ ds) = g→l d ∷ᵃ g→l-all ds

    g→l
      : G⟨ j , FLRules ⟩ ⊆ Deriv R
    g→l Refl = Refl
    g→l (Trans d d₁) = Trans (g→l d) (g→l d₁)
    g→l (ByRule (inl rr) ds) = ByRule (iFL rr) (g→l-all ds)
    g→l {Γ} d@(ByRule (inr (inl (lj-instance {b = b}))) ds) =
      transportCtx {L = Deriv R} {b = j b} (++-unit-r Γ)
        (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = j (j b)} {b = j b}
          (g⊆k d)
          (jj→j b))
    g→l {Γ} d@(ByRule (inr (inr (rj-instance {r = r} rr))) ds) =
      transportCtx {L = Deriv R} {b = j (Seq.obj (conclusion r))} (++-unit-r Γ)
        (Trans {U = Γ} {V₁ = []} {V₂ = []}
          {a = j (j (Seq.obj (conclusion r)))}
          {b = j (Seq.obj (conclusion r))}
          (g⊆k d)
          (jj→j (Seq.obj (conclusion r))))

cond2→cond3
  : ∀ {j R}
  → Theorem3-Cond2 j (Deriv R)
  → Theorem3-Cond3 j (Deriv R)
cond2→cond3 {j} {R} g⊆l = s· , s∧ , s⊸ , s›
  where
  s· : ∀ {a b} → Deriv R (singleton (j a `· j b)) (j (a `· b))
  s· {a} {b} = g⊆l (shiftCoreInG-FL (shift·-instance {a = a} {b = b}) []ᵃ)

  s∧ : ∀ {a b} → Deriv R (singleton (j a `∧ j b)) (j (a `∧ b))
  s∧ {a} {b} = g⊆l (shiftCoreInG-FL (shift∧-instance {a = a} {b = b}) []ᵃ)

  s⊸ : ∀ {a b} → Deriv R (singleton (a `⊸ j b)) (j (a `⊸ b))
  s⊸ {a} {b} = g⊆l (shiftCoreInG-FL (shift⊸-instance {a = a} {b = b}) []ᵃ)

  s› : ∀ {a b} → Deriv R (singleton (j b `› a)) (j (b `› a))
  s› {a} {b} = g⊆l (shiftCoreInG-FL (shift›-instance {a = a} {b = b}) []ᵃ)

cond3→cond2
  : ∀ {j R}
  → FLRules ⊆R R
  → Expansive j FLRules
  → LeftProgressiveR j FLRules ⊎ (RightProgressiveR j FLRules ⊎ BiProgressiveR j FLRules)
  → Theorem3-Cond3 j (Deriv R)
  → Theorem3-Cond2 j (Deriv R)
cond3→cond2 {j} {R} iFL e pn (s· , s∧ , s⊸ , s›) d = ext⊆l (g⊆ext d)
  where
  g⊆ext : G⟨ j , FLRules ⟩ ⊆ L⟨ ShiftCoreExt j FLRules ⟩
  g⊆ext = fst (lemma2-FL e pn)

  mutual

    ext⊆l-all
      : ∀ {ps}
      → PremisesHold (L⟨ ShiftCoreExt j FLRules ⟩) ps
      → PremisesHold (Deriv R) ps
    ext⊆l-all {ps = []} []ᵃ = []ᵃ
    ext⊆l-all {ps = p ∷ ps} (d ∷ᵃ ds) = ext⊆l d ∷ᵃ ext⊆l-all ds

    ext⊆l
      : L⟨ ShiftCoreExt j FLRules ⟩ ⊆ Deriv R
    ext⊆l Refl = Refl
    ext⊆l (Trans d d₁) = Trans (ext⊆l d) (ext⊆l d₁)
    ext⊆l (ByRule (inl rr) ds) = ByRule (iFL rr) (ext⊆l-all ds)
    ext⊆l (ByRule (inr (shift·-instance {a = a} {b = b})) []ᵃ) = s· {a} {b}
    ext⊆l (ByRule (inr (shift∧-instance {a = a} {b = b})) []ᵃ) = s∧ {a} {b}
    ext⊆l (ByRule (inr (shift⊸-instance {a = a} {b = b})) []ᵃ) = s⊸ {a} {b}
    ext⊆l (ByRule (inr (shift›-instance {a = a} {b = b})) []ᵃ) = s› {a} {b}

theorem3-proof
  : ∀ {j R}
  → FLRules ⊆R R
  → Expansive j FLRules
  → LeftProgressiveR j FLRules ⊎ (RightProgressiveR j FLRules ⊎ BiProgressiveR j FLRules)
  → Deriv R ⊆ M⟨ j , FLRules ⟩
  → (Theorem3-Cond1 j (Deriv R) ↔ Theorem3-Cond2 j (Deriv R))
    × (Theorem3-Cond2 j (Deriv R) ↔ Theorem3-Cond3 j (Deriv R))
theorem3-proof {j} {R} iFL e pn l⊆m =
  intro to12 from12
  ,
  intro to23 from23
  where
  to12 : Theorem3-Cond1 j (Deriv R) → Theorem3-Cond2 j (Deriv R)
  to12 = cond1→cond2 iFL e

  from12 : Theorem3-Cond2 j (Deriv R) → Theorem3-Cond1 j (Deriv R)
  from12 = cond2→cond1 e l⊆m

  to23 : Theorem3-Cond2 j (Deriv R) → Theorem3-Cond3 j (Deriv R)
  to23 = cond2→cond3

  from23 : Theorem3-Cond3 j (Deriv R) → Theorem3-Cond2 j (Deriv R)
  from23 = cond3→cond2 iFL e pn
