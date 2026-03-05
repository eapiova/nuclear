module Substructural.FL.Shifts where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.FL.Basic
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula
open import Cubical.Data.List.Properties using (++-unit-r)

private
  variable
    R : RuleSet
    U V Γ : Ctx
    a b : Formula
    j : Formula → Formula

Shift1 : (Formula → Formula) → Entailment → Type
Shift1 j L = L (singleton `1) (j `1)

Shift∧ : (Formula → Formula) → Entailment → Type
Shift∧ j L = ∀ {a b} → L (singleton (j a `∧ j b)) (j (a `∧ b))

Shift· : (Formula → Formula) → Entailment → Type
Shift· j L = ∀ {a b} → L (singleton (j a `· j b)) (j (a `· b))

Shift∨ : (Formula → Formula) → Entailment → Type
Shift∨ j L = ∀ {a b} → L (singleton (j a `∨ j b)) (j (a `∨ b))

Shift⊸ : (Formula → Formula) → Entailment → Type
Shift⊸ j L = ∀ {a b} → L (singleton (a `⊸ j b)) (j (a `⊸ b))

Shift› : (Formula → Formula) → Entailment → Type
Shift› j L = ∀ {a b} → L (singleton (j b `› a)) (j (b `› a))

R1-Kj : (Formula → Formula) → RuleSet → Type
R1-Kj j R = Kj j (L⟨ R ⟩) [] `1

R∨-Kj : (Formula → Formula) → RuleSet → Type
R∨-Kj j R =
  (∀ {U a b} → Kj j (L⟨ R ⟩) U a → Kj j (L⟨ R ⟩) U (a `∨ b))
  ×
  (∀ {U a b} → Kj j (L⟨ R ⟩) U b → Kj j (L⟨ R ⟩) U (a `∨ b))

R∧-Kj : (Formula → Formula) → RuleSet → Type
R∧-Kj j R =
  ∀ {U a b}
  → Kj j (L⟨ R ⟩) U a
  → Kj j (L⟨ R ⟩) U b
  → Kj j (L⟨ R ⟩) U (a `∧ b)

R·-Kj : (Formula → Formula) → RuleSet → Type
R·-Kj j R =
  ∀ {U V a b}
  → Kj j (L⟨ R ⟩) U a
  → Kj j (L⟨ R ⟩) V b
  → Kj j (L⟨ R ⟩) (U ++ V) (a `· b)

R⊸-Kj : (Formula → Formula) → RuleSet → Type
R⊸-Kj j R =
  ∀ {U a b}
  → Kj j (L⟨ R ⟩) (a ∷ U) b
  → Kj j (L⟨ R ⟩) U (a `⊸ b)

R›-Kj : (Formula → Formula) → RuleSet → Type
R›-Kj j R =
  ∀ {U a b}
  → Kj j (L⟨ R ⟩) (plug₁ U a []) b
  → Kj j (L⟨ R ⟩) U (b `› a)

shift1→R1-Kj
  : ∀ {j R}
  → FLRules ⊆R R
  → Shift1 j (L⟨ R ⟩)
  → R1-Kj j R
shift1→R1-Kj {j} {R} iFL s =
  Trans {U = []} {V₁ = []} {V₂ = []}
    (ByRule (iFL R1) []ᵃ)
    s

R1-Kj→shift1
  : ∀ {j R}
  → FLRules ⊆R R
  → R1-Kj j R
  → Shift1 j (L⟨ R ⟩)
R1-Kj→shift1 {j} {R} iFL r1 =
  ByRule (iFL (L1 {U = []} {V = []} {c = j `1})) (r1 ∷ᵃ []ᵃ)

shift∨→R∨-Kj
  : ∀ {j R}
  → FLRules ⊆R R
  → Shift∨ j (L⟨ R ⟩)
  → R∨-Kj j R
shift∨→R∨-Kj {j} {R} iFL s =
  to₁ , to₂
  where
  to₁ : ∀ {U a b} → Kj j (L⟨ R ⟩) U a → Kj j (L⟨ R ⟩) U (a `∨ b)
  to₁ {U} {a} {b} d =
    transportCtx {L = Deriv R} (++-unit-r U)
      (Trans {U = U} {V₁ = []} {V₂ = []}
        (ByRule (iFL (R∨₁ {U = U} {a = j a} {b = j b})) (d ∷ᵃ []ᵃ))
        s)

  to₂ : ∀ {U a b} → Kj j (L⟨ R ⟩) U b → Kj j (L⟨ R ⟩) U (a `∨ b)
  to₂ {U} {a} {b} d =
    transportCtx {L = Deriv R} (++-unit-r U)
      (Trans {U = U} {V₁ = []} {V₂ = []}
        (ByRule (iFL (R∨₂ {U = U} {a = j a} {b = j b})) (d ∷ᵃ []ᵃ))
        s)

R∨-Kj→shift∨
  : ∀ {j R}
  → FLRules ⊆R R
  → R∨-Kj j R
  → Shift∨ j (L⟨ R ⟩)
R∨-Kj→shift∨ {j} {R} iFL (r∨₁ , r∨₂) {a} {b} =
  ByRule
    (iFL (L∨ {U = []} {V = []} {a = j a} {b = j b} {c = j (a `∨ b)}))
    (fromA ∷ᵃ fromB ∷ᵃ []ᵃ)
  where
  fromA : Deriv R (singleton (j a)) (j (a `∨ b))
  fromA = r∨₁ Refl

  fromB : Deriv R (singleton (j b)) (j (a `∨ b))
  fromB = r∨₂ Refl

shift∧→R∧-Kj
  : ∀ {j R}
  → FLRules ⊆R R
  → Shift∧ j (L⟨ R ⟩)
  → R∧-Kj j R
shift∧→R∧-Kj {j} {R} iFL s {U} {a} {b} da db =
  transportCtx {L = Deriv R} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (iFL (R∧ {U = U} {a = j a} {b = j b})) (da ∷ᵃ db ∷ᵃ []ᵃ))
      s)

R∧-Kj→shift∧
  : ∀ {j R}
  → FLRules ⊆R R
  → R∧-Kj j R
  → Shift∧ j (L⟨ R ⟩)
R∧-Kj→shift∧ {j} {R} iFL r∧ {a} {b} =
  r∧ left right
  where
  left : Deriv R (singleton (j a `∧ j b)) (j a)
  left = ByRule (iFL (L∧₁ {U = []} {V = []} {a = j a} {b = j b} {c = j a})) (Refl ∷ᵃ []ᵃ)

  right : Deriv R (singleton (j a `∧ j b)) (j b)
  right = ByRule (iFL (L∧₂ {U = []} {V = []} {a = j a} {b = j b} {c = j b})) (Refl ∷ᵃ []ᵃ)

shift·→R·-Kj
  : ∀ {j R}
  → FLRules ⊆R R
  → Shift· j (L⟨ R ⟩)
  → R·-Kj j R
shift·→R·-Kj {j} {R} iFL s {U} {V} {a} {b} da db =
  transportCtx {L = Deriv R} (++-unit-r (U ++ V))
    (Trans {U = U ++ V} {V₁ = []} {V₂ = []}
      (ByRule (iFL (R· {U = U} {V = V} {a = j a} {b = j b})) (da ∷ᵃ db ∷ᵃ []ᵃ))
      s)

R·-Kj→shift·
  : ∀ {j R}
  → FLRules ⊆R R
  → R·-Kj j R
  → Shift· j (L⟨ R ⟩)
R·-Kj→shift· {j} {R} iFL r· {a} {b} =
  ByRule (iFL (L· {U = []} {V = []} {a = j a} {b = j b} {c = j (a `· b)})) (mid ∷ᵃ []ᵃ)
  where
  mid : Deriv R (j a ∷ j b ∷ []) (j (a `· b))
  mid = r· Refl Refl

shift⊸→R⊸-Kj
  : ∀ {j R}
  → FLRules ⊆R R
  → Shift⊸ j (L⟨ R ⟩)
  → R⊸-Kj j R
shift⊸→R⊸-Kj {j} {R} iFL s {U} {a} {b} d =
  transportCtx {L = Deriv R} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (iFL (R⊸ {U = U} {a = a} {b = j b})) (d ∷ᵃ []ᵃ))
      s)

R⊸-Kj→shift⊸
  : ∀ {j R}
  → FLRules ⊆R R
  → R⊸-Kj j R
  → Shift⊸ j (L⟨ R ⟩)
R⊸-Kj→shift⊸ {j} {R} iFL r⊸ {a} {b} =
  r⊸
    (ByRule
      (iFL (L⊸ {U = singleton a} {V = []} {W = []} {a = a} {b = j b} {c = j b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))

shift›→R›-Kj
  : ∀ {j R}
  → FLRules ⊆R R
  → Shift› j (L⟨ R ⟩)
  → R›-Kj j R
shift›→R›-Kj {j} {R} iFL s {U} {a} {b} d =
  transportCtx {L = Deriv R} (++-unit-r U)
    (Trans {U = U} {V₁ = []} {V₂ = []}
      (ByRule (iFL (R› {U = U} {a = a} {b = j b})) (d ∷ᵃ []ᵃ))
      s)

R›-Kj→shift›
  : ∀ {j R}
  → FLRules ⊆R R
  → R›-Kj j R
  → Shift› j (L⟨ R ⟩)
R›-Kj→shift› {j} {R} iFL r› {a} {b} =
  r›
    (ByRule
      (iFL (L› {U = singleton a} {V = []} {W = []} {a = a} {b = j b} {c = j b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))

theorem15
  : ∀ {j R}
  → FLRules ⊆R R
  → (R1-Kj j R ↔ Shift1 j (L⟨ R ⟩))
    × (R∨-Kj j R ↔ Shift∨ j (L⟨ R ⟩))
    × (R∧-Kj j R ↔ Shift∧ j (L⟨ R ⟩))
    × (R·-Kj j R ↔ Shift· j (L⟨ R ⟩))
    × (R⊸-Kj j R ↔ Shift⊸ j (L⟨ R ⟩))
    × (R›-Kj j R ↔ Shift› j (L⟨ R ⟩))
theorem15 {j} {R} iFL =
  intro (R1-Kj→shift1 {j} {R} iFL) (shift1→R1-Kj {j} {R} iFL)
  , intro (R∨-Kj→shift∨ {j} {R} iFL) (shift∨→R∨-Kj {j} {R} iFL)
  , intro (R∧-Kj→shift∧ {j} {R} iFL) (shift∧→R∧-Kj {j} {R} iFL)
  , intro (R·-Kj→shift· {j} {R} iFL) (shift·→R·-Kj {j} {R} iFL)
  , intro (R⊸-Kj→shift⊸ {j} {R} iFL) (shift⊸→R⊸-Kj {j} {R} iFL)
  , intro (R›-Kj→shift› {j} {R} iFL) (shift›→R›-Kj {j} {R} iFL)

lemma16-1
  : ∀ {j R}
  → FLRules ⊆R R
  → Nucleus j (L⟨ R ⟩)
  → Shift1 j (L⟨ R ⟩) × Shift∨ j (L⟨ R ⟩)
lemma16-1 {j} {R} iFL n = shift1 , shift∨
  where
  rjL : Rj j (L⟨ R ⟩)
  rjL = nucleus-rj n

  ljL : Lj j (L⟨ R ⟩)
  ljL = nucleus-lj n

  shift1 : Shift1 j (L⟨ R ⟩)
  shift1 =
    ByRule (iFL (L1 {U = []} {V = []} {c = j `1}))
      (rjL (ByRule (iFL R1) []ᵃ) ∷ᵃ []ᵃ)

  shift∨ : Shift∨ j (L⟨ R ⟩)
  shift∨ {a} {b} =
    ByRule
      (iFL (L∨ {U = []} {V = []} {a = j a} {b = j b} {c = j (a `∨ b)}))
      (left ∷ᵃ right ∷ᵃ []ᵃ)
    where
    left0 : Deriv R (singleton a) (j (a `∨ b))
    left0 = rjL (ByRule (iFL (R∨₁ {U = singleton a} {a = a} {b = b})) (Refl ∷ᵃ []ᵃ))

    left : Deriv R (singleton (j a)) (j (a `∨ b))
    left = ljL {U = []} {V = []} {a = a} {b = a `∨ b} left0

    right0 : Deriv R (singleton b) (j (a `∨ b))
    right0 = rjL (ByRule (iFL (R∨₂ {U = singleton b} {a = a} {b = b})) (Refl ∷ᵃ []ᵃ))

    right : Deriv R (singleton (j b)) (j (a `∨ b))
    right = ljL {U = []} {V = []} {a = b} {b = a `∨ b} right0

lemma16-2 : (Formula → Formula) → RuleSet → Type
lemma16-2 j R = Shift· j (L⟨ R ∪R CommRules ⟩)

lemma16-3 : (Formula → Formula) → RuleSet → Type
lemma16-3 j R = Shift∧ j (L⟨ R ∪R CommRules ∪R MonoRules ∪R ContrRules ⟩)

lemma16-4 : (Formula → Formula) → RuleSet → Type
lemma16-4 j R = Nucleus j (L⟨ R ⟩) → Shift· j (L⟨ R ⟩) → BiNucleus j (L⟨ R ⟩)

lemma16-4-proof
  : ∀ {j R}
  → Nucleus j (L⟨ R ⟩)
  → Shift· j (L⟨ R ⟩)
  → BiNucleus j (L⟨ R ⟩)
lemma16-4-proof n s = nucleus→biNucleus n

plug-singleton
  : ∀ (U V : Ctx) (a : Formula)
  → plug U V (singleton a) ≡ plug₁ U a V
plug-singleton U V a = refl

L⊸j-local : (Formula → Formula) → Entailment → Type
L⊸j-local j L =
  ∀ {U V W a b c}
  → L U (j a)
  → L (plug₁ W b V) (j c)
  → L (plug₁ (W ++ U) (a `⊸ b) V) (j c)

L›j-local : (Formula → Formula) → Entailment → Type
L›j-local j L =
  ∀ {U V W a b c}
  → L U (j a)
  → L (plug₁ W b V) (j c)
  → L (plug₁ W (b `› a) (U ++ V)) (j c)

lemma16-5 : (Formula → Formula) → RuleSet → Type
lemma16-5 j R =
  FLRules ⊆R R
  → BiNucleus j (L⟨ R ⟩)
  → L⊸j-local j (L⟨ R ⟩) × L›j-local j (L⟨ R ⟩)

lemma16-5-proof
  : ∀ {j R}
  → FLRules ⊆R R
  → BiNucleus j (L⟨ R ⟩)
  → L⊸j-local j (L⟨ R ⟩) × L›j-local j (L⟨ R ⟩)
lemma16-5-proof {j} {R} iFL bn =
  l⊸j
  ,
  l›j
  where
  rjL : Rj j (L⟨ R ⟩)
  rjL = biNucleus-rj bn

  ljL : Lj j (L⟨ R ⟩)
  ljL = biNucleus-lj bn

  map-⊸
    : ∀ {a b}
    → Deriv R (singleton (a `⊸ b)) (j a `⊸ j b)
  map-⊸ {a} {b} =
    ByRule (iFL (R⊸ {U = singleton (a `⊸ b)} {a = j a} {b = j b})) (d1 ∷ᵃ []ᵃ)
    where
    d0 : Deriv R (a ∷ (a `⊸ b) ∷ []) (j b)
    d0 = rjL (mp⊸-in {a = a} {b = b} iFL)

    d1 : Deriv R (j a ∷ (a `⊸ b) ∷ []) (j b)
    d1 = ljL {U = []} {V = singleton (a `⊸ b)} {a = a} {b = b} d0

  map-›
    : ∀ {a b}
    → Deriv R (singleton (b `› a)) (j b `› j a)
  map-› {a} {b} =
    ByRule (iFL (R› {U = singleton (b `› a)} {a = j a} {b = j b})) (d1 ∷ᵃ []ᵃ)
    where
    d0 : Deriv R ((b `› a) ∷ a ∷ []) (j b)
    d0 = rjL (mp›-in {a = a} {b = b} iFL)

    d1 : Deriv R ((b `› a) ∷ j a ∷ []) (j b)
    d1 = ljL {U = singleton (b `› a)} {V = []} {a = a} {b = b} d0

  l⊸j : L⊸j-local j (L⟨ R ⟩)
  l⊸j {U} {V} {W} {a} {b} {c} dU dWV =
    transportCtx {L = Deriv R} (plug-singleton (W ++ U) V (a `⊸ b))
      (Trans {U = singleton (a `⊸ b)} {V₁ = W ++ U} {V₂ = V}
        map⊸d
        core)
    where
    map⊸d : Deriv R (singleton (a `⊸ b)) (j a `⊸ j b)
    map⊸d = map-⊸ {a = a} {b = b}

    dWV' : Deriv R (plug₁ W (j b) V) (j c)
    dWV' = ljL {U = W} {V = V} {a = b} {b = c} dWV

    core : Deriv R (plug₁ (W ++ U) (j a `⊸ j b) V) (j c)
    core =
      ByRule
        (iFL (L⊸ {U = U} {V = V} {W = W} {a = j a} {b = j b} {c = j c}))
        (dU ∷ᵃ dWV' ∷ᵃ []ᵃ)

  l›j : L›j-local j (L⟨ R ⟩)
  l›j {U} {V} {W} {a} {b} {c} dU dWV =
    transportCtx {L = Deriv R} (plug-singleton W (U ++ V) (b `› a))
      (Trans {U = singleton (b `› a)} {V₁ = W} {V₂ = U ++ V}
        map›d
        core)
    where
    map›d : Deriv R (singleton (b `› a)) (j b `› j a)
    map›d = map-› {a = a} {b = b}

    dWV' : Deriv R (plug₁ W (j b) V) (j c)
    dWV' = ljL {U = W} {V = V} {a = b} {b = c} dWV

    core : Deriv R (plug₁ W (j b `› j a) (U ++ V)) (j c)
    core =
      ByRule
        (iFL (L› {U = U} {V = V} {W = W} {a = j a} {b = j b} {c = j c}))
        (dU ∷ᵃ dWV' ∷ᵃ []ᵃ)

lemma16-6 : (Formula → Formula) → RuleSet → Type
lemma16-6 j R =
  FLRules ⊆R R
  → Nucleus j (L⟨ R ⟩)
  → Shift· j (L⟨ R ⟩)
  → L⊸j-local j (L⟨ R ⟩)
    × L›j-local j (L⟨ R ⟩)
    × Transj j (L⟨ R ⟩)

lemma16-6-proof
  : ∀ {j R}
  → FLRules ⊆R R
  → Nucleus j (L⟨ R ⟩)
  → Shift· j (L⟨ R ⟩)
  → L⊸j-local j (L⟨ R ⟩)
    × L›j-local j (L⟨ R ⟩)
    × Transj j (L⟨ R ⟩)
lemma16-6-proof {j} {R} iFL n s =
  fst survive
  ,
  snd survive
  ,
  to (fst (snd (lemma6 {j = j} {R = R}))) (biNucleus-lj bn)
  where
  bn : BiNucleus j (L⟨ R ⟩)
  bn = lemma16-4-proof n s

  survive : L⊸j-local j (L⟨ R ⟩) × L›j-local j (L⟨ R ⟩)
  survive = lemma16-5-proof iFL bn

-- Full Lemma 16 package signature for downstream modules.
lemma16 : (Formula → Formula) → RuleSet → Type
lemma16 j R =
  (Nucleus j (L⟨ R ⟩) → Shift1 j (L⟨ R ⟩) × Shift∨ j (L⟨ R ⟩))
  × lemma16-2 j R
  × lemma16-3 j R
  × lemma16-4 j R
  × lemma16-5 j R
  × lemma16-6 j R

data ShiftCoreRules (j : Formula → Formula) : RuleSet where
  shift·-instance
    : ∀ {a b}
    → ShiftCoreRules j (mkRule [] (singleton (j a `· j b) ▷ j (a `· b)))
  shift∧-instance
    : ∀ {a b}
    → ShiftCoreRules j (mkRule [] (singleton (j a `∧ j b) ▷ j (a `∧ b)))
  shift⊸-instance
    : ∀ {a b}
    → ShiftCoreRules j (mkRule [] (singleton (a `⊸ j b) ▷ j (a `⊸ b)))
  shift›-instance
    : ∀ {a b}
    → ShiftCoreRules j (mkRule [] (singleton (j b `› a) ▷ j (b `› a)))

ShiftCoreExt : (Formula → Formula) → RuleSet → RuleSet
ShiftCoreExt j R = R ∪R ShiftCoreRules j

ShiftCoreDerivableInBase : (Formula → Formula) → RuleSet → Type
ShiftCoreDerivableInBase j R =
  ∀ {r}
  → ShiftCoreRules j r
  → RuleHoldsIn r (L⟨ R ⟩)

ShiftCoreDerivableInG : (Formula → Formula) → RuleSet → Type
ShiftCoreDerivableInG j R =
  ∀ {r}
  → ShiftCoreRules j r
  → RuleHoldsIn r (G⟨ j , R ⟩)

shiftCore-from-components
  : ∀ {j R}
  → Shift· j (L⟨ R ⟩)
  → Shift∧ j (L⟨ R ⟩)
  → Shift⊸ j (L⟨ R ⟩)
  → Shift› j (L⟨ R ⟩)
  → ShiftCoreDerivableInBase j R
shiftCore-from-components s· s∧ s⊸ s› shift·-instance []ᵃ = s·
shiftCore-from-components s· s∧ s⊸ s› shift∧-instance []ᵃ = s∧
shiftCore-from-components s· s∧ s⊸ s› shift⊸-instance []ᵃ = s⊸
shiftCore-from-components s· s∧ s⊸ s› shift›-instance []ᵃ = s›

shiftCore-base→G
  : ∀ {j R}
  → ShiftCoreDerivableInBase j R
  → ShiftCoreDerivableInG j R
shiftCore-base→G b shift·-instance []ᵃ = lift-base-into-G (b shift·-instance []ᵃ)
shiftCore-base→G b shift∧-instance []ᵃ = lift-base-into-G (b shift∧-instance []ᵃ)
shiftCore-base→G b shift⊸-instance []ᵃ = lift-base-into-G (b shift⊸-instance []ᵃ)
shiftCore-base→G b shift›-instance []ᵃ = lift-base-into-G (b shift›-instance []ᵃ)

mutual

  ext→g-all
    : ∀ {j R ps}
    → ShiftCoreDerivableInG j R
    → PremisesHold (L⟨ ShiftCoreExt j R ⟩) ps
    → PremisesHold (G⟨ j , R ⟩) ps
  ext→g-all {ps = []} s []ᵃ = []ᵃ
  ext→g-all {ps = p ∷ ps} s (d ∷ᵃ ds) = ext→g s d ∷ᵃ ext→g-all s ds

  ext→g
    : ∀ {j R}
    → ShiftCoreDerivableInG j R
    → L⟨ ShiftCoreExt j R ⟩ ⊆ G⟨ j , R ⟩
  ext→g s Refl = Refl
  ext→g s (Trans d d₁) = Trans (ext→g s d) (ext→g s d₁)
  ext→g s (ByRule (inl rr) ds) = ByRule (inl rr) (ext→g-all s ds)
  ext→g s (ByRule (inr sr) ds) = s sr (ext→g-all s ds)

mutual

  g→ext-all
    : ∀ {j R ps}
    → Lj j (L⟨ ShiftCoreExt j R ⟩)
    → (∀ {r} → R r → SurvivesAfter j r (ShiftCoreExt j R))
    → PremisesHold (G⟨ j , R ⟩) ps
    → PremisesHold (L⟨ ShiftCoreExt j R ⟩) ps
  g→ext-all {ps = []} lj surv []ᵃ = []ᵃ
  g→ext-all {ps = p ∷ ps} lj surv (d ∷ᵃ ds) = g→ext lj surv d ∷ᵃ g→ext-all lj surv ds

  g→ext
    : ∀ {j R}
    → Lj j (L⟨ ShiftCoreExt j R ⟩)
    → (∀ {r} → R r → SurvivesAfter j r (ShiftCoreExt j R))
    → G⟨ j , R ⟩ ⊆ L⟨ ShiftCoreExt j R ⟩
  g→ext lj surv Refl = Refl
  g→ext lj surv (Trans d d₁) = Trans (g→ext lj surv d) (g→ext lj surv d₁)
  g→ext lj surv (ByRule (inl rr) ds) = ByRule (inl rr) (g→ext-all lj surv ds)
  g→ext lj surv (ByRule (inr (inl lj-instance)) ds) =
    lj (All-lookup-head (g→ext-all lj surv ds))
  g→ext lj surv (ByRule (inr (inr (rj-instance rr))) ds) =
    surv rr (g→ext-all lj surv ds)

lemma17 : (Formula → Formula) → RuleSet → Type
lemma17 j R =
  Lj j (L⟨ ShiftCoreExt j R ⟩)
  → (∀ {r} → R r → SurvivesAfter j r (ShiftCoreExt j R))
  → ShiftCoreDerivableInG j R
  → (G⟨ j , R ⟩ ⊆ L⟨ ShiftCoreExt j R ⟩)
    × (L⟨ ShiftCoreExt j R ⟩ ⊆ G⟨ j , R ⟩)

lemma17-proof
  : ∀ {j R}
  → Lj j (L⟨ ShiftCoreExt j R ⟩)
  → (∀ {r} → R r → SurvivesAfter j r (ShiftCoreExt j R))
  → ShiftCoreDerivableInG j R
  → (G⟨ j , R ⟩ ⊆ L⟨ ShiftCoreExt j R ⟩)
    × (L⟨ ShiftCoreExt j R ⟩ ⊆ G⟨ j , R ⟩)
lemma17-proof lj surv s = g→ext lj surv , ext→g s

lemma17-from-base-shifts
  : ∀ {j R}
  → Lj j (L⟨ ShiftCoreExt j R ⟩)
  → (∀ {r} → R r → SurvivesAfter j r (ShiftCoreExt j R))
  → ShiftCoreDerivableInBase j R
  → (G⟨ j , R ⟩ ⊆ L⟨ ShiftCoreExt j R ⟩)
    × (L⟨ ShiftCoreExt j R ⟩ ⊆ G⟨ j , R ⟩)
lemma17-from-base-shifts lj surv s =
  lemma17-proof lj surv (shiftCore-base→G s)

Theorem19-Cond1 : (Formula → Formula) → Entailment → Type
Theorem19-Cond1 j L = ∀ {Γ a} → M⟨ j , FLRules ⟩ Γ a ↔ L Γ (j a)

Theorem19-Cond2 : (Formula → Formula) → Entailment → Type
Theorem19-Cond2 j L = G⟨ j , FLRules ⟩ ⊆ L

Theorem19-Cond3 : (Formula → Formula) → Entailment → Type
Theorem19-Cond3 j L =
  (∀ {a b} → L (singleton (j a `· j b)) (j (a `· b)))
  × (∀ {a b} → L (singleton (j a `∧ j b)) (j (a `∧ b)))
  × (∀ {a b} → L (singleton (a `⊸ j b)) (j (a `⊸ b)))
  × (∀ {a b} → L (singleton (j b `› a)) (j (b `› a)))

theorem19 : (j : Formula → Formula) (L : Entailment) → Type
theorem19 j L =
  (RightNucleus j FL ⊎ (LeftNucleus j FL ⊎ BiNucleus j FL))
  → L ⊆ M⟨ j , FLRules ⟩
  → (Theorem19-Cond1 j L ↔ Theorem19-Cond2 j L)
    × (Theorem19-Cond2 j L ↔ Theorem19-Cond3 j L)
