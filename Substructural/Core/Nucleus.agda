{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Nucleus {ℓ} (S : Set ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S
open import Substructural.Core.Derivation S
open import Cubical.Data.List.Properties using (++-unit-r)

-- Definition 1: rule Rj.
Rj : (S → S) → RuleSchema
Rj j L = ∀ {Γ a} → L Γ a → L Γ (j a)

Reflj : (S → S) → RuleSchema
Reflj j L = ∀ a → L (singleton a) (j a)

suffix : Ctx → S → Ctx
suffix U a = plug₁ U a []

prefix : S → Ctx → Ctx
prefix a U = plug₁ [] a U

-- Definition 1: Lj (and its left/right specializations).
Lj : (S → S) → RuleSchema
Lj j L = ∀ {U V a b} → L (plug₁ U a V) (j b) → L (plug₁ U (j a) V) (j b)

Ljleft : (S → S) → RuleSchema
Ljleft j L = ∀ {U a b} → L (suffix U a) (j b) → L (suffix U (j a)) (j b)

Ljright : (S → S) → RuleSchema
Ljright j L = ∀ {U a b} → L (prefix a U) (j b) → L (prefix (j a) U) (j b)

Transj : (S → S) → RuleSchema
Transj j L =
  ∀ {W U V a b}
  → L W (j a)
  → L (plug₁ U a V) (j b)
  → L (plug U V W) (j b)

-- Definition 5 / Lemma 6(3): stability and its Lj+ counterpart.
j-stab : (S → S) → RuleSchema
j-stab j L = ∀ a → L (singleton (j a)) a

Lj+ : (S → S) → RuleSchema
Lj+ j L = ∀ {U V a b} → L (plug₁ U a V) b → L (plug₁ U (j a) V) b

record Nucleus (f : S → S) (L : Entailment) : Type ℓ where
  constructor mkNucleus
  field
    expansiveN : Rj f L
    progressiveN : Lj f L

record StableNucleus (f : S → S) (L : Entailment) : Type ℓ where
  constructor mkStableNucleus
  field
    expansiveStable : Rj f L
    stableN : Lj+ f L

nucleus-rj : ∀ {f L} → Nucleus f L → Rj f L
nucleus-rj = Nucleus.expansiveN

nucleus-lj : ∀ {f L} → Nucleus f L → Lj f L
nucleus-lj = Nucleus.progressiveN

stable-rj : ∀ {f L} → StableNucleus f L → Rj f L
stable-rj = StableNucleus.expansiveStable

stable-lj+ : ∀ {f L} → StableNucleus f L → Lj+ f L
stable-lj+ = StableNucleus.stableN

stable→nucleus : ∀ {f L} → StableNucleus f L → Nucleus f L
stable→nucleus {f} {L} s = mkNucleus (stable-rj s) λ {U} {V} {a} {b} d → stable-lj+ s d

record LeftNucleus (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkLeftNucleus
  field
    expansiveLN : Rj j L
    progressiveLN : Ljleft j L

record RightNucleus (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkRightNucleus
  field
    expansiveRN : Rj j L
    progressiveRN : Ljright j L

record BiNucleus (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkBiNucleus
  field
    expansiveBN : Rj j L
    progressiveBN : Lj j L

leftNucleus-rj : ∀ {j L} → LeftNucleus j L → Rj j L
leftNucleus-rj = LeftNucleus.expansiveLN

leftNucleus-ljleft : ∀ {j L} → LeftNucleus j L → Ljleft j L
leftNucleus-ljleft = LeftNucleus.progressiveLN

rightNucleus-rj : ∀ {j L} → RightNucleus j L → Rj j L
rightNucleus-rj = RightNucleus.expansiveRN

rightNucleus-ljright : ∀ {j L} → RightNucleus j L → Ljright j L
rightNucleus-ljright = RightNucleus.progressiveRN

biNucleus-rj : ∀ {j L} → BiNucleus j L → Rj j L
biNucleus-rj = BiNucleus.expansiveBN

biNucleus-lj : ∀ {j L} → BiNucleus j L → Lj j L
biNucleus-lj = BiNucleus.progressiveBN

biNucleus→nucleus : ∀ {j L} → BiNucleus j L → Nucleus j L
biNucleus→nucleus b = mkNucleus (biNucleus-rj b) (biNucleus-lj b)

nucleus→biNucleus : ∀ {j L} → Nucleus j L → BiNucleus j L
nucleus→biNucleus n = mkBiNucleus (nucleus-rj n) (nucleus-lj n)

-- Expansiveness over the base derivability relation.
record Expansive (j : S → S) (R : RuleSet) : Type ℓ where
  constructor mkExpansive
  field
    expansive : Rj j (Deriv R)

record LeftProgressive (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkLeftProgressive
  field
    leftProgressive : Ljleft j L

record LeftProgressiveR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkLeftProgressiveR
  field
    leftProgressiveR : ∀ {R'} → R ⊆R R' → Ljleft j (Deriv R')

record RightProgressive (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkRightProgressive
  field
    rightProgressive : Ljright j L

record RightProgressiveR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkRightProgressiveR
  field
    rightProgressiveR : ∀ {R'} → R ⊆R R' → Ljright j (Deriv R')

record BiProgressive (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkBiProgressive
  field
    biProgressive : Lj j L

record BiProgressiveR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkBiProgressiveR
  field
    biProgressiveR : ∀ {R'} → R ⊆R R' → Lj j (Deriv R')


-- ESPANSIVE needed for NUCLEI

onBase-Expansive : ∀ {j R} → Expansive j R → Rj j (Deriv R)
onBase-Expansive e = Expansive.expansive e

lift-Expansive
  : ∀ {j R R'}
  → Expansive j R
  → R ⊆R R'
  → Rj j (Deriv R')
lift-Expansive {j} {R} {R'} e i {Γ} {a} d =
  subst (λ X → Deriv R' X (j a)) (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} d (lift-⊆R i (Expansive.expansive e Refl)))

onBase-LeftProgressiveR : ∀ {j R} → LeftProgressiveR j R → Ljleft j (Deriv R)
onBase-LeftProgressiveR n = LeftProgressiveR.leftProgressiveR n (λ r → r)

lift-LeftProgressiveR
  : ∀ {j R R'}
  → LeftProgressiveR j R
  → R ⊆R R'
  → Ljleft j (Deriv R')
lift-LeftProgressiveR n i = LeftProgressiveR.leftProgressiveR n i

onBase-RightProgressiveR : ∀ {j R} → RightProgressiveR j R → Ljright j (Deriv R)
onBase-RightProgressiveR n = RightProgressiveR.rightProgressiveR n (λ r → r)

lift-RightProgressiveR
  : ∀ {j R R'}
  → RightProgressiveR j R
  → R ⊆R R'
  → Ljright j (Deriv R')
lift-RightProgressiveR n i = RightProgressiveR.rightProgressiveR n i

onBase-BiProgressiveR : ∀ {j R} → BiProgressiveR j R → Lj j (Deriv R)
onBase-BiProgressiveR n = BiProgressiveR.biProgressiveR n (λ r → r)

lift-BiProgressiveR
  : ∀ {j R R'}
  → BiProgressiveR j R
  → R ⊆R R'
  → Lj j (Deriv R')
lift-BiProgressiveR n i = BiProgressiveR.biProgressiveR n i

rj : (S → S) → Rule → Rule
rj = mapSuccRule

-- Definition 5: "rule r survives after j" means rj is admissible.
-- r must be admissible !!!
SurvivesAfter : (S → S) → Rule → RuleSet → Type ℓ
SurvivesAfter j r R = AdmissibleRule (rj j r) R
