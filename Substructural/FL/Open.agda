module Substructural.FL.Open where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.FL.Basic
open import Substructural.FL.Shifts
open import Substructural.FL.Theorem19
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula using (transportCtx)
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)

oR : Formula → Formula
oR a = `0 `⊸ (`0 `· a)

oL : Formula → Formula
oL a = (a `· `0) `› `0

RoR : Rj oR FL
RoR {Γ} {a} d =
  ByRule (R⊸ {U = Γ} {a = `0} {b = `0 `· a}) (d0 ∷ᵃ []ᵃ)
  where
  d0 : FL (`0 ∷ Γ) (`0 `· a)
  d0 =
    ByRule
      (R· {U = singleton `0} {V = Γ} {a = `0} {b = a})
      (Refl ∷ᵃ d ∷ᵃ []ᵃ)

RoR-R : ∀ {R'} → FLRules ⊆R R' → Rj oR (Deriv R')
RoR-R iFL {Γ} {a} d =
  ByRule (iFL (R⊸ {U = Γ} {a = `0} {b = `0 `· a})) (d0 ∷ᵃ []ᵃ)
  where
  d0 : Deriv _ (`0 ∷ Γ) (`0 `· a)
  d0 =
    ByRule
      (iFL (R· {U = singleton `0} {V = Γ} {a = `0} {b = a}))
      (Refl ∷ᵃ d ∷ᵃ []ᵃ)

LoR-right-helper : ∀ {a b} → FL (oR a ∷ (a `⊸ oR b) ∷ []) (oR b)
LoR-right-helper {a} {b} =
  ByRule
    (R⊸ {U = oR a ∷ (a `⊸ oR b) ∷ []} {a = `0} {b = `0 `· b})
    (d4 ∷ᵃ []ᵃ)
  where
  d1 : FL (`0 ∷ oR b ∷ []) (`0 `· b)
  d1 =
    ByRule
      (L⊸
        {U = singleton `0}
        {V = []}
        {W = []}
        {a = `0}
        {b = `0 `· b}
        {c = `0 `· b})
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  d2 : FL (`0 ∷ a ∷ (a `⊸ oR b) ∷ []) (`0 `· b)
  d2 =
    ByRule
      (L⊸
        {U = singleton a}
        {V = []}
        {W = singleton `0}
        {a = a}
        {b = oR b}
        {c = `0 `· b})
      (Refl ∷ᵃ d1 ∷ᵃ []ᵃ)

  d3 : FL ((`0 `· a) ∷ (a `⊸ oR b) ∷ []) (`0 `· b)
  d3 =
    ByRule
      (L· {U = []} {V = singleton (a `⊸ oR b)} {a = `0} {b = a} {c = `0 `· b})
      (d2 ∷ᵃ []ᵃ)

  d4 : FL (`0 ∷ oR a ∷ (a `⊸ oR b) ∷ []) (`0 `· b)
  d4 =
    ByRule
      (L⊸
        {U = singleton `0}
        {V = singleton (a `⊸ oR b)}
        {W = []}
        {a = `0}
        {b = `0 `· a}
        {c = `0 `· b})
      (Refl ∷ᵃ d3 ∷ᵃ []ᵃ)

LoR-right-helper-R : ∀ {R'} → FLRules ⊆R R' → ∀ {a b} → Deriv R' (oR a ∷ (a `⊸ oR b) ∷ []) (oR b)
LoR-right-helper-R iFL {a} {b} =
  ByRule
    (iFL (R⊸ {U = oR a ∷ (a `⊸ oR b) ∷ []} {a = `0} {b = `0 `· b}))
    (d4 ∷ᵃ []ᵃ)
  where
  d1 : Deriv _ (`0 ∷ oR b ∷ []) (`0 `· b)
  d1 =
    ByRule
      (iFL
        (L⊸
          {U = singleton `0}
          {V = []}
          {W = []}
          {a = `0}
          {b = `0 `· b}
          {c = `0 `· b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  d2 : Deriv _ (`0 ∷ a ∷ (a `⊸ oR b) ∷ []) (`0 `· b)
  d2 =
    ByRule
      (iFL
        (L⊸
          {U = singleton a}
          {V = []}
          {W = singleton `0}
          {a = a}
          {b = oR b}
          {c = `0 `· b}))
      (Refl ∷ᵃ d1 ∷ᵃ []ᵃ)

  d3 : Deriv _ ((`0 `· a) ∷ (a `⊸ oR b) ∷ []) (`0 `· b)
  d3 =
    ByRule
      (iFL (L· {U = []} {V = singleton (a `⊸ oR b)} {a = `0} {b = a} {c = `0 `· b}))
      (d2 ∷ᵃ []ᵃ)

  d4 : Deriv _ (`0 ∷ oR a ∷ (a `⊸ oR b) ∷ []) (`0 `· b)
  d4 =
    ByRule
      (iFL
        (L⊸
          {U = singleton `0}
          {V = singleton (a `⊸ oR b)}
          {W = []}
          {a = `0}
          {b = `0 `· a}
          {c = `0 `· b}))
      (Refl ∷ᵃ d3 ∷ᵃ []ᵃ)

LoR-right : Ljright oR FL
LoR-right {U} {a} {b} d =
  transportCtx {L = FL} (cong ((oR a) ∷_) (++-unit-r U))
    (Trans {U = U} {V₁ = singleton (oR a)} {V₂ = []} d1 LoR-right-helper)
  where
  d1 : FL U (a `⊸ oR b)
  d1 = ByRule (R⊸ {U = U} {a = a} {b = oR b}) (d ∷ᵃ []ᵃ)

LoR-right-R : ∀ {R'} → FLRules ⊆R R' → Ljright oR (Deriv R')
LoR-right-R iFL {U} {a} {b} d =
  transportCtx {L = Deriv _} (cong ((oR a) ∷_) (++-unit-r U))
    (Trans {U = U} {V₁ = singleton (oR a)} {V₂ = []} d1 (LoR-right-helper-R iFL))
  where
  d1 : Deriv _ U (a `⊸ oR b)
  d1 = ByRule (iFL (R⊸ {U = U} {a = a} {b = oR b})) (d ∷ᵃ []ᵃ)

oR-right-nucleus : RightNucleus oR FL
oR-right-nucleus = mkRightNucleus RoR LoR-right

RoL : Rj oL FL
RoL {Γ} {a} d =
  ByRule (R› {U = Γ} {a = `0} {b = a `· `0}) (d0 ∷ᵃ []ᵃ)
  where
  d0 : FL (Γ ++ (`0 ∷ [])) (a `· `0)
  d0 = ByRule (R· {U = Γ} {V = singleton `0} {a = a} {b = `0}) (d ∷ᵃ Refl ∷ᵃ []ᵃ)

RoL-R : ∀ {R'} → FLRules ⊆R R' → Rj oL (Deriv R')
RoL-R iFL {Γ} {a} d =
  ByRule (iFL (R› {U = Γ} {a = `0} {b = a `· `0})) (d0 ∷ᵃ []ᵃ)
  where
  d0 : Deriv _ (Γ ++ (`0 ∷ [])) (a `· `0)
  d0 = ByRule (iFL (R· {U = Γ} {V = singleton `0} {a = a} {b = `0})) (d ∷ᵃ Refl ∷ᵃ []ᵃ)

oL-expansive : Rj oL FL
oL-expansive = RoL

LoL-left : Ljleft oL FL
LoL-left {U} {a} {b} d =
  ByRule (R› {U = suffix U (oL a)} {a = `0} {b = b `· `0}) (d4 ∷ᵃ []ᵃ)
  where
  iFL : FLRules ⊆R FLRules
  iFL rr = rr

  d0 : FL ((suffix U a) ++ (`0 ∷ [])) (b `· `0)
  d0 = R›-invert iFL d

  p1 : ((suffix U a) ++ (`0 ∷ [])) ≡ U ++ (a ∷ `0 ∷ [])
  p1 = ++-assoc U (a ∷ []) (`0 ∷ [])

  d1 : FL (U ++ (a ∷ `0 ∷ [])) (b `· `0)
  d1 = transportCtx {L = FL} p1 d0

  d2 : FL (U ++ ((a `· `0) ∷ [])) (b `· `0)
  d2 =
    ByRule
      (L· {U = U} {V = []} {a = a} {b = `0} {c = b `· `0})
      (d1 ∷ᵃ []ᵃ)

  d3 : FL (U ++ (oL a ∷ `0 ∷ [])) (b `· `0)
  d3 =
    Trans
      {U = oL a ∷ `0 ∷ []}
      {V₁ = U}
      {V₂ = []}
      (mp› {a = `0} {b = a `· `0})
      d2

  p2 : ((suffix U (oL a)) ++ (`0 ∷ [])) ≡ U ++ (oL a ∷ `0 ∷ [])
  p2 = ++-assoc U (oL a ∷ []) (`0 ∷ [])

  d4 : FL ((suffix U (oL a)) ++ (`0 ∷ [])) (b `· `0)
  d4 = transportCtx {L = FL} (sym p2) d3

LoL-left-R : ∀ {R'} → FLRules ⊆R R' → Ljleft oL (Deriv R')
LoL-left-R iFL {U} {a} {b} d =
  ByRule (iFL (R› {U = suffix U (oL a)} {a = `0} {b = b `· `0})) (d4 ∷ᵃ []ᵃ)
  where
  d0 : Deriv _ ((suffix U a) ++ (`0 ∷ [])) (b `· `0)
  d0 = R›-invert iFL d

  p1 : ((suffix U a) ++ (`0 ∷ [])) ≡ U ++ (a ∷ `0 ∷ [])
  p1 = ++-assoc U (a ∷ []) (`0 ∷ [])

  d1 : Deriv _ (U ++ (a ∷ `0 ∷ [])) (b `· `0)
  d1 = transportCtx {L = Deriv _} p1 d0

  d2 : Deriv _ (U ++ ((a `· `0) ∷ [])) (b `· `0)
  d2 =
    ByRule
      (iFL (L· {U = U} {V = []} {a = a} {b = `0} {c = b `· `0}))
      (d1 ∷ᵃ []ᵃ)

  d3 : Deriv _ (U ++ (oL a ∷ `0 ∷ [])) (b `· `0)
  d3 =
    Trans
      {U = oL a ∷ `0 ∷ []}
      {V₁ = U}
      {V₂ = []}
      (lift-⊆R iFL (mp› {a = `0} {b = a `· `0}))
      d2

  p2 : ((suffix U (oL a)) ++ (`0 ∷ [])) ≡ U ++ (oL a ∷ `0 ∷ [])
  p2 = ++-assoc U (oL a ∷ []) (`0 ∷ [])

  d4 : Deriv _ ((suffix U (oL a)) ++ (`0 ∷ [])) (b `· `0)
  d4 = transportCtx {L = Deriv _} (sym p2) d3

oL-left-nucleus : LeftNucleus oL FL
oL-left-nucleus = mkLeftNucleus RoL LoL-left

remark7 : RightNucleus oR FL × LeftNucleus oL FL
remark7 = oR-right-nucleus , oL-left-nucleus

oR-expansive-R : Expansive oR FLRules
oR-expansive-R = mkExpansive (RoR-R (λ r → r))

oR-rightProgressiveR : RightProgressiveR oR FLRules
oR-rightProgressiveR = mkRightProgressiveR LoR-right-R

oL-expansive-R : Expansive oL FLRules
oL-expansive-R = mkExpansive (RoL-R (λ r → r))

oL-leftProgressiveR : LeftProgressiveR oL FLRules
oL-leftProgressiveR = mkLeftProgressiveR LoL-left-R

oR-t3 : ∀ {R} → FLRules ⊆R R → theorem3 oR (Deriv R)
oR-t3 iFL _ l⊆m = theorem3-proof iFL oR-expansive-R (inr (inl oR-rightProgressiveR)) l⊆m

oL-t3 : ∀ {R} → FLRules ⊆R R → theorem3 oL (Deriv R)
oL-t3 iFL _ l⊆m = theorem3-proof iFL oL-expansive-R (inl oL-leftProgressiveR) l⊆m

oR-bridge
  : ∀ {R Γ a}
  → FLRules ⊆R R
  → (Deriv R Γ (oR a) ↔ Deriv R (`0 ∷ Γ) (`0 `· a))
oR-bridge {R} {Γ} {a} iFL =
  intro to' from'
  where
  to' : Deriv R Γ (oR a) → Deriv R (`0 ∷ Γ) (`0 `· a)
  to' = R⊸-invert iFL

  from' : Deriv R (`0 ∷ Γ) (`0 `· a) → Deriv R Γ (oR a)
  from' d = ByRule (iFL (R⊸ {U = Γ} {a = `0} {b = `0 `· a})) (d ∷ᵃ []ᵃ)

oL-bridge
  : ∀ {R Γ a}
  → FLRules ⊆R R
  → (Deriv R Γ (oL a) ↔ Deriv R (Γ ++ (`0 ∷ [])) (a `· `0))
oL-bridge {R} {Γ} {a} iFL =
  intro to' from'
  where
  to' : Deriv R Γ (oL a) → Deriv R (Γ ++ (`0 ∷ [])) (a `· `0)
  to' = R›-invert iFL

  from' : Deriv R (Γ ++ (`0 ∷ [])) (a `· `0) → Deriv R Γ (oL a)
  from' d = ByRule (iFL (R› {U = Γ} {a = `0} {b = a `· `0})) (d ∷ᵃ []ᵃ)

OR-Cond1 : Entailment → Type
OR-Cond1 L = ∀ {Γ a} → M⟨ oR , FLRules ⟩ Γ a ↔ L (`0 ∷ Γ) (`0 `· a)

OR-Cond2 : Entailment → Type
OR-Cond2 L = G⟨ oR , FLRules ⟩ ⊆ L

OR-Cond3 : Entailment → Type
OR-Cond3 L =
  (∀ {a b} → L (`0 ∷ (oR a `· oR b) ∷ []) (`0 `· (a `· b)))
  × (∀ {a b} → L (`0 ∷ (oR a `∧ oR b) ∷ []) (`0 `· (a `∧ b)))
  × (∀ {a b} → L (`0 ∷ (a `⊸ oR b) ∷ []) (`0 `· (a `⊸ b)))
  × (∀ {a b} → L (`0 ∷ (oR b `› a) ∷ []) (`0 `· (b `› a)))

OL-Cond1 : Entailment → Type
OL-Cond1 L = ∀ {Γ a} → M⟨ oL , FLRules ⟩ Γ a ↔ L (Γ ++ (`0 ∷ [])) (a `· `0)

OL-Cond2 : Entailment → Type
OL-Cond2 L = G⟨ oL , FLRules ⟩ ⊆ L

OL-Cond3 : Entailment → Type
OL-Cond3 L =
  (∀ {a b} → L ((oL a `· oL b) ∷ `0 ∷ []) ((a `· b) `· `0))
  × (∀ {a b} → L ((oL a `∧ oL b) ∷ `0 ∷ []) ((a `∧ b) `· `0))
  × (∀ {a b} → L ((a `⊸ oL b) ∷ `0 ∷ []) ((a `⊸ b) `· `0))
  × (∀ {a b} → L ((oL b `› a) ∷ `0 ∷ []) ((b `› a) `· `0))

corollary3 : (L : Entailment) → Type
corollary3 L =
  (L ⊆ M⟨ oR , FLRules ⟩
  → (OR-Cond1 L ↔ OR-Cond2 L)
    × (OR-Cond2 L ↔ OR-Cond3 L))
  ×
  (L ⊆ M⟨ oL , FLRules ⟩
  → (OL-Cond1 L ↔ OL-Cond2 L)
    × (OL-Cond2 L ↔ OL-Cond3 L))

or-cond1-full→paper
  : ∀ {R}
  → FLRules ⊆R R
  → Theorem3-Cond1 oR (Deriv R)
  → OR-Cond1 (Deriv R)
or-cond1-full→paper {R} iFL full {Γ} {a} =
  intro to' from'
  where
  br = oR-bridge {R = R} {Γ = Γ} {a = a} iFL

  to' : M⟨ oR , FLRules ⟩ Γ a → Deriv R (`0 ∷ Γ) (`0 `· a)
  to' d = to br (to (full {Γ = Γ} {a = a}) d)

  from' : Deriv R (`0 ∷ Γ) (`0 `· a) → M⟨ oR , FLRules ⟩ Γ a
  from' d = from (full {Γ = Γ} {a = a}) (from br d)

or-cond1-paper→full
  : ∀ {R}
  → FLRules ⊆R R
  → OR-Cond1 (Deriv R)
  → Theorem3-Cond1 oR (Deriv R)
or-cond1-paper→full {R} iFL paper {Γ} {a} =
  intro to' from'
  where
  br = oR-bridge {R = R} {Γ = Γ} {a = a} iFL

  to' : M⟨ oR , FLRules ⟩ Γ a → Deriv R Γ (oR a)
  to' d = from br (to (paper {Γ = Γ} {a = a}) d)

  from' : Deriv R Γ (oR a) → M⟨ oR , FLRules ⟩ Γ a
  from' d = from (paper {Γ = Γ} {a = a}) (to br d)

or-cond3-full→paper
  : ∀ {R}
  → FLRules ⊆R R
  → Theorem3-Cond3 oR (Deriv R)
  → OR-Cond3 (Deriv R)
or-cond3-full→paper {R} iFL (s· , s∧ , s⊸ , s›) =
  to· , to∧ , to⊸ , to›
  where
  to· : ∀ {a b} → Deriv R (`0 ∷ (oR a `· oR b) ∷ []) (`0 `· (a `· b))
  to· {a} {b} =
    to (oR-bridge {R = R} {Γ = singleton (oR a `· oR b)} {a = a `· b} iFL) (s· {a} {b})

  to∧ : ∀ {a b} → Deriv R (`0 ∷ (oR a `∧ oR b) ∷ []) (`0 `· (a `∧ b))
  to∧ {a} {b} =
    to (oR-bridge {R = R} {Γ = singleton (oR a `∧ oR b)} {a = a `∧ b} iFL) (s∧ {a} {b})

  to⊸ : ∀ {a b} → Deriv R (`0 ∷ (a `⊸ oR b) ∷ []) (`0 `· (a `⊸ b))
  to⊸ {a} {b} =
    to (oR-bridge {R = R} {Γ = singleton (a `⊸ oR b)} {a = a `⊸ b} iFL) (s⊸ {a} {b})

  to› : ∀ {a b} → Deriv R (`0 ∷ (oR b `› a) ∷ []) (`0 `· (b `› a))
  to› {a} {b} =
    to (oR-bridge {R = R} {Γ = singleton (oR b `› a)} {a = b `› a} iFL) (s› {a} {b})

or-cond3-paper→full
  : ∀ {R}
  → FLRules ⊆R R
  → OR-Cond3 (Deriv R)
  → Theorem3-Cond3 oR (Deriv R)
or-cond3-paper→full {R} iFL (s· , s∧ , s⊸ , s›) =
  from· , from∧ , from⊸ , from›
  where
  from· : ∀ {a b} → Deriv R (singleton (oR a `· oR b)) (oR (a `· b))
  from· {a} {b} =
    from (oR-bridge {R = R} {Γ = singleton (oR a `· oR b)} {a = a `· b} iFL) (s· {a} {b})

  from∧ : ∀ {a b} → Deriv R (singleton (oR a `∧ oR b)) (oR (a `∧ b))
  from∧ {a} {b} =
    from (oR-bridge {R = R} {Γ = singleton (oR a `∧ oR b)} {a = a `∧ b} iFL) (s∧ {a} {b})

  from⊸ : ∀ {a b} → Deriv R (singleton (a `⊸ oR b)) (oR (a `⊸ b))
  from⊸ {a} {b} =
    from (oR-bridge {R = R} {Γ = singleton (a `⊸ oR b)} {a = a `⊸ b} iFL) (s⊸ {a} {b})

  from› : ∀ {a b} → Deriv R (singleton (oR b `› a)) (oR (b `› a))
  from› {a} {b} =
    from (oR-bridge {R = R} {Γ = singleton (oR b `› a)} {a = b `› a} iFL) (s› {a} {b})

ol-cond1-full→paper
  : ∀ {R}
  → FLRules ⊆R R
  → Theorem3-Cond1 oL (Deriv R)
  → OL-Cond1 (Deriv R)
ol-cond1-full→paper {R} iFL full {Γ} {a} =
  intro to' from'
  where
  br = oL-bridge {R = R} {Γ = Γ} {a = a} iFL

  to' : M⟨ oL , FLRules ⟩ Γ a → Deriv R (Γ ++ (`0 ∷ [])) (a `· `0)
  to' d = to br (to (full {Γ = Γ} {a = a}) d)

  from' : Deriv R (Γ ++ (`0 ∷ [])) (a `· `0) → M⟨ oL , FLRules ⟩ Γ a
  from' d = from (full {Γ = Γ} {a = a}) (from br d)

ol-cond1-paper→full
  : ∀ {R}
  → FLRules ⊆R R
  → OL-Cond1 (Deriv R)
  → Theorem3-Cond1 oL (Deriv R)
ol-cond1-paper→full {R} iFL paper {Γ} {a} =
  intro to' from'
  where
  br = oL-bridge {R = R} {Γ = Γ} {a = a} iFL

  to' : M⟨ oL , FLRules ⟩ Γ a → Deriv R Γ (oL a)
  to' d = from br (to (paper {Γ = Γ} {a = a}) d)

  from' : Deriv R Γ (oL a) → M⟨ oL , FLRules ⟩ Γ a
  from' d = from (paper {Γ = Γ} {a = a}) (to br d)

ol-cond3-full→paper
  : ∀ {R}
  → FLRules ⊆R R
  → Theorem3-Cond3 oL (Deriv R)
  → OL-Cond3 (Deriv R)
ol-cond3-full→paper {R} iFL (s· , s∧ , s⊸ , s›) =
  to· , to∧ , to⊸ , to›
  where
  to· : ∀ {a b} → Deriv R ((oL a `· oL b) ∷ `0 ∷ []) ((a `· b) `· `0)
  to· {a} {b} =
    to (oL-bridge {R = R} {Γ = singleton (oL a `· oL b)} {a = a `· b} iFL) (s· {a} {b})

  to∧ : ∀ {a b} → Deriv R ((oL a `∧ oL b) ∷ `0 ∷ []) ((a `∧ b) `· `0)
  to∧ {a} {b} =
    to (oL-bridge {R = R} {Γ = singleton (oL a `∧ oL b)} {a = a `∧ b} iFL) (s∧ {a} {b})

  to⊸ : ∀ {a b} → Deriv R ((a `⊸ oL b) ∷ `0 ∷ []) ((a `⊸ b) `· `0)
  to⊸ {a} {b} =
    to (oL-bridge {R = R} {Γ = singleton (a `⊸ oL b)} {a = a `⊸ b} iFL) (s⊸ {a} {b})

  to› : ∀ {a b} → Deriv R ((oL b `› a) ∷ `0 ∷ []) ((b `› a) `· `0)
  to› {a} {b} =
    to (oL-bridge {R = R} {Γ = singleton (oL b `› a)} {a = b `› a} iFL) (s› {a} {b})

ol-cond3-paper→full
  : ∀ {R}
  → FLRules ⊆R R
  → OL-Cond3 (Deriv R)
  → Theorem3-Cond3 oL (Deriv R)
ol-cond3-paper→full {R} iFL (s· , s∧ , s⊸ , s›) =
  from· , from∧ , from⊸ , from›
  where
  from· : ∀ {a b} → Deriv R (singleton (oL a `· oL b)) (oL (a `· b))
  from· {a} {b} =
    from (oL-bridge {R = R} {Γ = singleton (oL a `· oL b)} {a = a `· b} iFL) (s· {a} {b})

  from∧ : ∀ {a b} → Deriv R (singleton (oL a `∧ oL b)) (oL (a `∧ b))
  from∧ {a} {b} =
    from (oL-bridge {R = R} {Γ = singleton (oL a `∧ oL b)} {a = a `∧ b} iFL) (s∧ {a} {b})

  from⊸ : ∀ {a b} → Deriv R (singleton (a `⊸ oL b)) (oL (a `⊸ b))
  from⊸ {a} {b} =
    from (oL-bridge {R = R} {Γ = singleton (a `⊸ oL b)} {a = a `⊸ b} iFL) (s⊸ {a} {b})

  from› : ∀ {a b} → Deriv R (singleton (oL b `› a)) (oL (b `› a))
  from› {a} {b} =
    from (oL-bridge {R = R} {Γ = singleton (oL b `› a)} {a = b `› a} iFL) (s› {a} {b})

corollary3-from-theorem3
  : ∀ {R}
  → FLRules ⊆R R
  → theorem3 oR (Deriv R)
  → theorem3 oL (Deriv R)
  → corollary3 (Deriv R)
corollary3-from-theorem3 {R} iFL t19R t19L =
  leftPart
  ,
  rightPart
  where
  rn-oR : RightNucleus oR FL
  rn-oR = fst remark7

  ln-oL : LeftNucleus oL FL
  ln-oL = snd remark7

  leftPart
    : Deriv R ⊆ M⟨ oR , FLRules ⟩
    → (OR-Cond1 (Deriv R) ↔ OR-Cond2 (Deriv R))
      × (OR-Cond2 (Deriv R) ↔ OR-Cond3 (Deriv R))
  leftPart l⊆m =
    eq12
    ,
    intro to23 from23
    where
    t : (Theorem3-Cond1 oR (Deriv R) ↔ Theorem3-Cond2 oR (Deriv R))
        × (Theorem3-Cond2 oR (Deriv R) ↔ Theorem3-Cond3 oR (Deriv R))
    t = t19R (inj₁ rn-oR) l⊆m

    eq12full : Theorem3-Cond1 oR (Deriv R) ↔ OR-Cond2 (Deriv R)
    eq12full = fst t

    eq23full : OR-Cond2 (Deriv R) ↔ Theorem3-Cond3 oR (Deriv R)
    eq23full = snd t

    eq12 : OR-Cond1 (Deriv R) ↔ OR-Cond2 (Deriv R)
    eq12 =
      intro
        (λ c1 → to eq12full (or-cond1-paper→full iFL c1))
        (λ c2 → or-cond1-full→paper iFL (from eq12full c2))

    to23 : OR-Cond2 (Deriv R) → OR-Cond3 (Deriv R)
    to23 c2 = or-cond3-full→paper iFL (to eq23full c2)

    from23 : OR-Cond3 (Deriv R) → OR-Cond2 (Deriv R)
    from23 c3 = from eq23full (or-cond3-paper→full iFL c3)

  rightPart
    : Deriv R ⊆ M⟨ oL , FLRules ⟩
    → (OL-Cond1 (Deriv R) ↔ OL-Cond2 (Deriv R))
      × (OL-Cond2 (Deriv R) ↔ OL-Cond3 (Deriv R))
  rightPart l⊆m =
    eq12
    ,
    intro to23 from23
    where
    t : (Theorem3-Cond1 oL (Deriv R) ↔ Theorem3-Cond2 oL (Deriv R))
        × (Theorem3-Cond2 oL (Deriv R) ↔ Theorem3-Cond3 oL (Deriv R))
    t = t19L (inj₂ (inj₁ ln-oL)) l⊆m

    eq12full : Theorem3-Cond1 oL (Deriv R) ↔ OL-Cond2 (Deriv R)
    eq12full = fst t

    eq23full : OL-Cond2 (Deriv R) ↔ Theorem3-Cond3 oL (Deriv R)
    eq23full = snd t

    eq12 : OL-Cond1 (Deriv R) ↔ OL-Cond2 (Deriv R)
    eq12 =
      intro
        (λ c1 → to eq12full (ol-cond1-paper→full iFL c1))
        (λ c2 → ol-cond1-full→paper iFL (from eq12full c2))

    to23 : OL-Cond2 (Deriv R) → OL-Cond3 (Deriv R)
    to23 c2 = ol-cond3-full→paper iFL (to eq23full c2)

    from23 : OL-Cond3 (Deriv R) → OL-Cond2 (Deriv R)
    from23 c3 = from eq23full (ol-cond3-paper→full iFL c3)
