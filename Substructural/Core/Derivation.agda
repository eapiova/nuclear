{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Derivation {ℓ} (S : Set ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S

-- Glivenko_substructural.pdf, Section 2:
-- entailment relation as a predicate Γ ▷ a.
Entailment : Type (ℓ-suc ℓ)
Entailment = Ctx → S → Type ℓ

PremisesHold : Entailment → List Seq → Type ℓ
PremisesHold L ps = All (λ p → L (Seq.ctx p) (Seq.obj p)) ps

ConclusionHold : Entailment → Rule → Type ℓ
ConclusionHold L r = L (Seq.ctx (conclusion r)) (Seq.obj (conclusion r))

data Deriv (R : RuleSet) : Entailment where
  -- Structural rule Refl (Section 2).
  Refl : ∀ {a} → Deriv R (singleton a) a
  -- Structural rule Trans (Section 2).
  Trans
    : ∀ {U V₁ V₂ a b}
    → Deriv R U a
    → Deriv R (plug₁ V₁ a V₂) b
    → Deriv R (plug V₁ V₂ U) b
  -- Generic non-structural rule application (Section 2).
  ByRule
    : ∀ {r}
    → R r
    → PremisesHold (Deriv R) (premises r)
    → ConclusionHold (Deriv R) r

infix 4 _⊆_

_⊆_ : Entailment → Entailment → Type ℓ
L ⊆ L' = ∀ {Γ a} → L Γ a → L' Γ a

mutual

  liftAll-⊆R
    : ∀ {R R' ps}
    → R ⊆R R'
    → PremisesHold (Deriv R) ps
    → PremisesHold (Deriv R') ps
  liftAll-⊆R {ps = []} i []ᵃ = []ᵃ
  liftAll-⊆R {ps = p ∷ ps} i (d ∷ᵃ ds) = lift-⊆R i d ∷ᵃ liftAll-⊆R i ds

  lift-⊆R : ∀ {R R'} → R ⊆R R' → Deriv R ⊆ Deriv R'
  lift-⊆R i (Refl {a}) = Refl
  lift-⊆R i (Trans d e) = Trans (lift-⊆R i d) (lift-⊆R i e)
  lift-⊆R i (ByRule rr ds) = ByRule (i rr) (liftAll-⊆R i ds)

record DerivableRule (r : Rule) (L : Entailment) : Type ℓ where
  constructor mkDerivableRule
  field
    derive : PremisesHold L (premises r) → ConclusionHold L r

-- We keep admissibility separate from derivability (paper-aligned API choice).
record AdmissibleRule (r : Rule) (L : Entailment) : Type ℓ where
  constructor mkAdmissibleRule
  field
    admit : PremisesHold L (premises r) → ConclusionHold L r

RuleSchema : Type (ℓ-suc ℓ)
RuleSchema = Entailment → Type ℓ

DerivableSchema : Type (ℓ-suc ℓ)
DerivableSchema = RuleSchema

AdmissibleSchema : Type (ℓ-suc ℓ)
AdmissibleSchema = RuleSchema

admissible→derivable
  : ∀ {r L}
  → AdmissibleRule r L
  → DerivableRule r L
admissible→derivable a = mkDerivableRule (AdmissibleRule.admit a)

derivable→admissible
  : ∀ {r L}
  → DerivableRule r L
  → AdmissibleRule r L
derivable→admissible d = mkAdmissibleRule (DerivableRule.derive d)

rule-is-derivable
  : ∀ {R r}
  → R r
  → DerivableRule r (Deriv R)
rule-is-derivable rr = mkDerivableRule (ByRule rr)

rule-is-admissible
  : ∀ {R r}
  → R r
  → AdmissibleRule r (Deriv R)
rule-is-admissible rr = mkAdmissibleRule (ByRule rr)
