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
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)

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

-- On a singleton context, any progressive form gives the Lj replacement.
private
  lj-singleton
    : ∀ {j R R'}
    → R ⊆R R'
    → LeftProgressiveR j R ⊎ (RightProgressiveR j R ⊎ BiProgressiveR j R)
    → ∀ {c d} → Deriv R' (singleton c) (j d) → Deriv R' (singleton (j c)) (j d)
  lj-singleton i (inl lp) = lift-LeftProgressiveR lp i {U = []}
  lj-singleton i (inr (inl rp)) = lift-RightProgressiveR rp i {U = []}
  lj-singleton i (inr (inr bp)) = lift-BiProgressiveR bp i {U = []} {V = []}

lemma16-2-proof
  : ∀ {j R}
  → FLRules ⊆R R
  → Expansive j R
  → LeftProgressiveR j R ⊎ (RightProgressiveR j R ⊎ BiProgressiveR j R)
  → Shift· j (L⟨ R ∪R CommRules ⟩)
-- Case: LeftProgressiveR — use Ljleft + Comm twice
lemma16-2-proof {j} {R} iFL e (inl lp) {a} {b} =
  ByRule (iFL' (L· {U = []} {V = []} {a = j a} {b = j b})) (d5 ∷ᵃ []ᵃ)
  where
  iFL' : FLRules ⊆R (R ∪R CommRules)
  iFL' rr = inl (iFL rr)
  rj' : Rj j (Deriv (R ∪R CommRules))
  rj' = lift-Expansive e inj₁
  ljl : Ljleft j (Deriv (R ∪R CommRules))
  ljl = lift-LeftProgressiveR lp inj₁
  comm : Comm (Deriv (R ∪R CommRules))
  comm = comm-from-rules inj₂
  -- a, b ⊢ j(a·b) by R· + Rj
  d0 : Deriv (R ∪R CommRules) (a ∷ b ∷ []) (j (a `· b))
  d0 = rj' (ByRule (iFL' (R· {U = singleton a} {V = singleton b})) (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))
  -- a, jb ⊢ j(a·b) by Ljleft (replace last)
  d1 : Deriv (R ∪R CommRules) (a ∷ j b ∷ []) (j (a `· b))
  d1 = ljl {U = singleton a} {a = b} {b = a `· b} d0
  -- jb, a ⊢ j(a·b) by Comm
  d2 : Deriv (R ∪R CommRules) (j b ∷ a ∷ []) (j (a `· b))
  d2 = comm {U₁ = []} {U₂ = []} {a₁ = a} {a₂ = j b} {b = j (a `· b)} d1
  -- jb, ja ⊢ j(a·b) by Ljleft (replace last)
  d3 : Deriv (R ∪R CommRules) (j b ∷ j a ∷ []) (j (a `· b))
  d3 = ljl {U = singleton (j b)} {a = a} {b = a `· b} d2
  -- ja, jb ⊢ j(a·b) by Comm
  d5 : Deriv (R ∪R CommRules) (j a ∷ j b ∷ []) (j (a `· b))
  d5 = comm {U₁ = []} {U₂ = []} {a₁ = j b} {a₂ = j a} {b = j (a `· b)} d3
-- Case: RightProgressiveR — use Ljright + Comm twice
lemma16-2-proof {j} {R} iFL e (inr (inl rp)) {a} {b} =
  ByRule (iFL' (L· {U = []} {V = []} {a = j a} {b = j b})) (d5 ∷ᵃ []ᵃ)
  where
  iFL' : FLRules ⊆R (R ∪R CommRules)
  iFL' rr = inl (iFL rr)
  rj' : Rj j (Deriv (R ∪R CommRules))
  rj' = lift-Expansive e inj₁
  ljr : Ljright j (Deriv (R ∪R CommRules))
  ljr = lift-RightProgressiveR rp inj₁
  comm : Comm (Deriv (R ∪R CommRules))
  comm = comm-from-rules inj₂
  d0 : Deriv (R ∪R CommRules) (a ∷ b ∷ []) (j (a `· b))
  d0 = rj' (ByRule (iFL' (R· {U = singleton a} {V = singleton b})) (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))
  -- ja, b ⊢ j(a·b) by Ljright (replace first)
  d1 : Deriv (R ∪R CommRules) (j a ∷ b ∷ []) (j (a `· b))
  d1 = ljr {U = singleton b} {a = a} {b = a `· b} d0
  -- b, ja ⊢ j(a·b) by Comm
  d2 : Deriv (R ∪R CommRules) (b ∷ j a ∷ []) (j (a `· b))
  d2 = comm {U₁ = []} {U₂ = []} {a₁ = j a} {a₂ = b} {b = j (a `· b)} d1
  -- jb, ja ⊢ j(a·b) by Ljright (replace first)
  d3 : Deriv (R ∪R CommRules) (j b ∷ j a ∷ []) (j (a `· b))
  d3 = ljr {U = singleton (j a)} {a = b} {b = a `· b} d2
  -- ja, jb ⊢ j(a·b) by Comm
  d5 : Deriv (R ∪R CommRules) (j a ∷ j b ∷ []) (j (a `· b))
  d5 = comm {U₁ = []} {U₂ = []} {a₁ = j b} {a₂ = j a} {b = j (a `· b)} d3
-- Case: BiProgressiveR — full Lj, no Comm needed
lemma16-2-proof {j} {R} iFL e (inr (inr bp)) {a} {b} =
  ByRule (iFL' (L· {U = []} {V = []} {a = j a} {b = j b})) (d3 ∷ᵃ []ᵃ)
  where
  iFL' : FLRules ⊆R (R ∪R CommRules)
  iFL' rr = inl (iFL rr)
  rj' : Rj j (Deriv (R ∪R CommRules))
  rj' = lift-Expansive e inj₁
  lj' : Lj j (Deriv (R ∪R CommRules))
  lj' = lift-BiProgressiveR bp inj₁
  d0 : Deriv (R ∪R CommRules) (a ∷ b ∷ []) (j (a `· b))
  d0 = rj' (ByRule (iFL' (R· {U = singleton a} {V = singleton b})) (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))
  -- ja, b ⊢ j(a·b) by Lj at U=[], V=[b]
  d1 : Deriv (R ∪R CommRules) (j a ∷ b ∷ []) (j (a `· b))
  d1 = lj' {U = []} {V = singleton b} d0
  -- ja, jb ⊢ j(a·b) by Lj at U=[ja], V=[]
  d3 : Deriv (R ∪R CommRules) (j a ∷ j b ∷ []) (j (a `· b))
  d3 = lj' {U = singleton (j a)} {V = []} d1

lemma16-3-proof
  : ∀ {j R}
  → FLRules ⊆R R
  → Expansive j R
  → LeftProgressiveR j R ⊎ (RightProgressiveR j R ⊎ BiProgressiveR j R)
  → Shift∧ j (L⟨ R ∪R CommRules ∪R MonoRules ∪R ContrRules ⟩)
lemma16-3-proof {j} {R} iFL e pn {a} {b} =
  transportCtx {L = Deriv R'} (++-unit-r (singleton (j a `∧ j b)))
    (Trans {U = singleton (j a `∧ j b)} {V₁ = []} {V₂ = []} mid bridge)
  where
  R' : RuleSet
  R' = R ∪R CommRules ∪R MonoRules ∪R ContrRules
  iFL' : FLRules ⊆R R'
  iFL' rr = inl (iFL rr)
  iMono : MonoRules ⊆R R'
  iMono rr = inr (inr (inl rr))
  iContr : ContrRules ⊆R R'
  iContr rr = inr (inr (inr rr))
  iR : R ⊆R R'
  iR rr = inl rr
  -- Embed R ∪R CommRules into R'
  embed : (R ∪R CommRules) ⊆R R'
  embed (inl rr) = inl rr
  embed (inr cr) = inr (inl cr)
  rj' : Rj j (Deriv R')
  rj' = lift-Expansive e iR
  -- [ja ∧ jb] ⊢ ja · jb  via remark13
  step∧→· : Deriv R' (singleton (j a `∧ j b)) (j a `· j b)
  step∧→· = remark13-1-∧→· iFL' iMono iContr
  -- [ja · jb] ⊢ j(a · b)  via lemma16-2 lifted to R'
  step-shift· : Deriv R' (singleton (j a `· j b)) (j (a `· b))
  step-shift· = lift-⊆R embed (lemma16-2-proof iFL e pn)
  -- [ja ∧ jb] ⊢ j(a · b)  by Trans
  mid : Deriv R' (singleton (j a `∧ j b)) (j (a `· b))
  mid = transportCtx {L = Deriv R'} (++-unit-r (singleton (j a `∧ j b)))
    (Trans {U = singleton (j a `∧ j b)} {V₁ = []} {V₂ = []} step∧→· step-shift·)
  -- [a · b] ⊢ a ∧ b  via remark13
  step·→∧ : Deriv R' (singleton (a `· b)) (a `∧ b)
  step·→∧ = remark13-1-·→∧ iFL' iMono iContr
  -- [a · b] ⊢ j(a ∧ b)  by Rj
  stepRj : Deriv R' (singleton (a `· b)) (j (a `∧ b))
  stepRj = rj' step·→∧
  -- [j(a · b)] ⊢ j(a ∧ b)  by Lj on singleton
  bridge : Deriv R' (singleton (j (a `· b))) (j (a `∧ b))
  bridge = lj-singleton iR pn stepRj

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

-- ============================================================================
-- Item (4) of lem-shifts-FL: LeftNucleus + Shift· → full Lj
-- ============================================================================

-- Left-associative fold of a formula with a context.
-- foldCtx a [v₁,...,vₙ] = ((...(a·v₁)·v₂)·...)·vₙ
foldCtx : Formula → Ctx → Formula
foldCtx a [] = a
foldCtx a (v ∷ V) = foldCtx (a `· v) V

-- Iterated L·: fold antecedent from left.
-- From U, a, V ⊢ c derive U, foldCtx(a,V) ⊢ c.
foldL-·
  : ∀ {R c}
  → FLRules ⊆R R
  → (U : Ctx) (a : Formula) (V : Ctx)
  → Deriv R (plug₁ U a V) c
  → Deriv R (suffix U (foldCtx a V)) c
foldL-· iFL U a [] d = d
foldL-· iFL U a (v ∷ V) d =
  foldL-· iFL U (a `· v) V
    (ByRule (iFL (L· {U = U} {V = V} {a = a} {b = v})) (d ∷ᵃ []ᵃ))

-- Iterated R· + Rj + shift·: build j-version of fold.
-- Derive j(a), V ⊢ j(foldCtx(a,V)).
foldR-shift·
  : ∀ {j R}
  → FLRules ⊆R R
  → Rj j (Deriv R)
  → Shift· j (Deriv R)
  → (a : Formula) (V : Ctx)
  → Deriv R (j a ∷ V) (j (foldCtx a V))
foldR-shift· iFL rj s· a [] = Refl
foldR-shift· {j} iFL rj s· a (v ∷ V) =
  Trans {U = j a ∷ v ∷ []} {V₁ = []} {V₂ = V}
    step-ja·v
    (foldR-shift· iFL rj s· (a `· v) V)
  where
  step-R· : Deriv _ (j a ∷ v ∷ []) (j a `· j v)
  step-R· =
    ByRule (iFL (R· {U = singleton (j a)} {V = singleton v} {a = j a} {b = j v}))
      (Refl ∷ᵃ rj Refl ∷ᵃ []ᵃ)

  step-ja·v : Deriv _ (j a ∷ v ∷ []) (j (a `· v))
  step-ja·v =
    transportCtx {L = Deriv _} {b = j (a `· v)} (++-unit-r (j a ∷ v ∷ []))
      (Trans {U = j a ∷ v ∷ []} {V₁ = []} {V₂ = []}
        step-R·
        s·)

-- Paper item (4): Ljleft + Shift· → full Lj.
ljleft+shift·→lj
  : ∀ {j R}
  → FLRules ⊆R R
  → Rj j (Deriv R)
  → Ljleft j (Deriv R)
  → Shift· j (Deriv R)
  → Lj j (Deriv R)
ljleft+shift·→lj iFL rj ljl s· {U} {[]} {a} {b} d = ljl d
ljleft+shift·→lj {j} iFL rj ljl s· {U} {v ∷ V} {a} {b} d =
  transportCtx {L = Deriv _} {b = j b} (cong (U ++_) (++-unit-r (j a ∷ v ∷ V)))
    (Trans {U = j a ∷ v ∷ V} {V₁ = U} {V₂ = []}
      (foldR-shift· iFL rj s· a (v ∷ V))
      (ljl (foldL-· iFL U a (v ∷ V) d)))

-- Iterated L· with suffix: fold from position a in context, carrying W after.
-- From U, a, V, W ⊢ c derive U, foldCtx(a,V), W ⊢ c.
foldL-·-prefix
  : ∀ {R c}
  → FLRules ⊆R R
  → (U : Ctx) (a : Formula) (V : Ctx) (W : Ctx)
  → Deriv R (U ++ a ∷ V ++ W) c
  → Deriv R (U ++ foldCtx a V ∷ W) c
foldL-·-prefix iFL U a [] W d = d
foldL-·-prefix iFL U a (v ∷ V) W d =
  foldL-·-prefix iFL U (a `· v) V W
    (ByRule (iFL (L· {U = U} {V = V ++ W} {a = a} {b = v})) (d ∷ᵃ []ᵃ))

-- Iterated R· + Rj + shift· with j at both ends:
-- j(w), W, j(x) ⊢ j(foldCtx(w, W ++ [x])).
foldR-shift·-prefix
  : ∀ {j R}
  → FLRules ⊆R R
  → Rj j (Deriv R)
  → Shift· j (Deriv R)
  → (w : Formula) (W : Ctx) (x : Formula)
  → Deriv R (j w ∷ W ++ singleton (j x)) (j (foldCtx w (W ++ singleton x)))
foldR-shift·-prefix {j} iFL rj s· w [] x =
  transportCtx {L = Deriv _} {b = j (w `· x)} (++-unit-r (j w ∷ singleton (j x)))
    (Trans {U = j w ∷ singleton (j x)} {V₁ = []} {V₂ = []}
      (ByRule (iFL (R· {U = singleton (j w)} {V = singleton (j x)}))
        (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))
      s·)
foldR-shift·-prefix {j} iFL rj s· w (v ∷ W) x =
  Trans {U = j w ∷ v ∷ []} {V₁ = []} {V₂ = W ++ singleton (j x)}
    step-jw·v
    (foldR-shift·-prefix iFL rj s· (w `· v) W x)
  where
  step-R· : Deriv _ (j w ∷ v ∷ []) (j w `· j v)
  step-R· =
    ByRule (iFL (R· {U = singleton (j w)} {V = singleton v}))
      (Refl ∷ᵃ rj Refl ∷ᵃ []ᵃ)
  step-jw·v : Deriv _ (j w ∷ v ∷ []) (j (w `· v))
  step-jw·v =
    transportCtx {L = Deriv _} {b = j (w `· v)} (++-unit-r (j w ∷ v ∷ []))
      (Trans {U = j w ∷ v ∷ []} {V₁ = []} {V₂ = []}
        step-R·
        s·)

-- Symmetric: Ljright + Shift· → full Lj.
ljright+shift·→lj
  : ∀ {j R}
  → FLRules ⊆R R
  → Rj j (Deriv R)
  → Ljright j (Deriv R)
  → Shift· j (Deriv R)
  → Lj j (Deriv R)
ljright+shift·→lj iFL rj ljr s· {[]} {V} {a} {b} d = ljr d
ljright+shift·→lj {j} iFL rj ljr s· {u ∷ U} {V} {a} {b} d =
  transportCtx {L = Deriv _} {b = j b} (cong (u ∷_) (++-assoc U (singleton (j a)) V))
    (Trans {U = u ∷ U ++ singleton (j a)} {V₁ = []} {V₂ = V}
      unfold
      (ljr (foldL-·-prefix iFL [] u (U ++ singleton a) V
        (transportCtx {L = Deriv _} {b = j b} (cong (u ∷_) (sym (++-assoc U (singleton a) V))) d))))
  where
  unfold : Deriv _ (u ∷ U ++ singleton (j a)) (j (foldCtx u (U ++ singleton a)))
  unfold =
    Trans {U = singleton u} {V₁ = []} {V₂ = U ++ singleton (j a)}
      (rj Refl)
      (foldR-shift·-prefix iFL rj s· u U a)
