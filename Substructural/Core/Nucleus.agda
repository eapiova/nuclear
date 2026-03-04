{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Nucleus {ℓ} (S : Set ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S
open import Substructural.Core.Derivation S

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

record Expansive (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkExpansive
  field
    expansive : Rj j L

-- Extension-stable assumptions used for Proposition 10 / Theorem 11. PENSARE A COSA STAVO FACENDO
record ExpansiveR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkExpansiveR
  field
    expansiveR : ∀ {R'} → R ⊆R R' → Rj j (Deriv R')

record LeftNucleus (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkLeftNucleus
  field
    leftNucleus : Ljleft j L

record LeftNucleusR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkLeftNucleusR
  field
    leftNucleusR : ∀ {R'} → R ⊆R R' → Ljleft j (Deriv R')

record RightNucleus (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkRightNucleus
  field
    rightNucleus : Ljright j L

record RightNucleusR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkRightNucleusR
  field
    rightNucleusR : ∀ {R'} → R ⊆R R' → Ljright j (Deriv R')

record BiNucleus (j : S → S) (L : Entailment) : Type ℓ where
  constructor mkBiNucleus
  field
    biNucleus : Lj j L

record BiNucleusR (j : S → S) (R : RuleSet) : Type (ℓ-suc ℓ) where
  constructor mkBiNucleusR
  field
    biNucleusR : ∀ {R'} → R ⊆R R' → Lj j (Deriv R')


-- ESPANSIVE needed for NUCLEI

onBase-ExpansiveR : ∀ {j R} → ExpansiveR j R → Rj j (Deriv R)
onBase-ExpansiveR e = ExpansiveR.expansiveR e (λ r → r)

lift-ExpansiveR
  : ∀ {j R R'}
  → ExpansiveR j R
  → R ⊆R R'
  → Rj j (Deriv R')
lift-ExpansiveR e i = ExpansiveR.expansiveR e i

onBase-LeftNucleusR : ∀ {j R} → LeftNucleusR j R → Ljleft j (Deriv R)
onBase-LeftNucleusR n = LeftNucleusR.leftNucleusR n (λ r → r)

lift-LeftNucleusR
  : ∀ {j R R'}
  → LeftNucleusR j R
  → R ⊆R R'
  → Ljleft j (Deriv R')
lift-LeftNucleusR n i = LeftNucleusR.leftNucleusR n i

onBase-RightNucleusR : ∀ {j R} → RightNucleusR j R → Ljright j (Deriv R)
onBase-RightNucleusR n = RightNucleusR.rightNucleusR n (λ r → r)

lift-RightNucleusR
  : ∀ {j R R'}
  → RightNucleusR j R
  → R ⊆R R'
  → Ljright j (Deriv R')
lift-RightNucleusR n i = RightNucleusR.rightNucleusR n i

onBase-BiNucleusR : ∀ {j R} → BiNucleusR j R → Lj j (Deriv R)
onBase-BiNucleusR n = BiNucleusR.biNucleusR n (λ r → r)

lift-BiNucleusR
  : ∀ {j R R'}
  → BiNucleusR j R
  → R ⊆R R'
  → Lj j (Deriv R')
lift-BiNucleusR n i = BiNucleusR.biNucleusR n i

rj : (S → S) → Rule → Rule
rj = mapSuccRule

-- Definition 5: "rule r survives after j" means rj is admissible.
-- r must be admissible !!!
SurvivesAfter : (S → S) → Rule → RuleSet → Type ℓ
SurvivesAfter j r R = AdmissibleRule (rj j r) R
