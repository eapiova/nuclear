open import Cubical.Core.Primitives

module Substructural.Core.Derivation {ℓ} (S : Type ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S

-- Glivenko_substructural.pdf, Section 2:
-- entailment relation as a predicate Γ ▷ a.
Entailment : Type (ℓ-suc ℓ)
Entailment = Ctx → S → Type ℓ

infix 2 _⊢_▷_

_⊢_▷_ : Entailment → Ctx → S → Type ℓ
L ⊢ Γ ▷ a = L Γ a

PremisesHold : Entailment → List Seq → Type ℓ
PremisesHold L ps = All (λ p → L ⊢ Seq.ctx p ▷ Seq.obj p) ps

ConclusionHold : Entailment → Rule → Type ℓ
ConclusionHold L r = L ⊢ Seq.ctx (conclusion r) ▷ Seq.obj (conclusion r)

data Deriv (R : RuleSet) : Entailment where
  -- Structural rule Refl (Section 2).
  Refl : ∀ {a} → Deriv R ⊢ singleton a ▷ a
  -- Structural rule Trans (Section 2).
  Trans
    : ∀ {U V₁ V₂ a b}
    → Deriv R ⊢ U ▷ a
    → Deriv R ⊢ V₁ ++ a ∷ V₂ ▷ b
    → Deriv R ⊢ V₁ ++ U ++ V₂ ▷ b
  -- Generic non-structural rule application (Section 2).
  ByRule
    : ∀ {r}
    → R r
    → PremisesHold (Deriv R) (premises r)
    → ConclusionHold (Deriv R) r

infix 4 _⊆_

_⊆_ : Entailment → Entailment → Type ℓ
L ⊆ L' = ∀ {Γ a} → L ⊢ Γ ▷ a → L' ⊢ Γ ▷ a

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

RuleHoldsIn : Rule → Entailment → Type ℓ
RuleHoldsIn r L = PremisesHold L (premises r) → ConclusionHold L r

record ModelOf (R : RuleSet) (L : Entailment) : Type ℓ where
  constructor mkModelOf
  field
    modelRefl : ∀ {a} → L ⊢ singleton a ▷ a
    modelTrans
      : ∀ {U V₁ V₂ a b}
      → L ⊢ U ▷ a
      → L ⊢ V₁ ++ a ∷ V₂ ▷ b
      → L ⊢ V₁ ++ U ++ V₂ ▷ b
    modelRule : ∀ {r} → R r → RuleHoldsIn r L

deriv-is-model : ∀ {R} → ModelOf R (Deriv R)
deriv-is-model = mkModelOf Refl Trans ByRule

DerivableRule : Rule → RuleSet → Type (ℓ-suc ℓ)
DerivableRule r R = ∀ {L} → ModelOf R L → RuleHoldsIn r L

AdmissibleRule : Rule → RuleSet → Type ℓ
AdmissibleRule r R = RuleHoldsIn r (Deriv R)

RuleSchema : Type (ℓ-suc ℓ)
RuleSchema = Entailment → Type ℓ

DerivableSchema : Type (ℓ-suc ℓ)
DerivableSchema = RuleSchema

AdmissibleSchema : Type (ℓ-suc ℓ)
AdmissibleSchema = RuleSchema

derivable→admissible
  : ∀ {r R}
  → DerivableRule r R
  → AdmissibleRule r R
derivable→admissible d = d deriv-is-model

rule-is-derivable
  : ∀ {R r}
  → R r
  → DerivableRule r R
rule-is-derivable rr m ps = ModelOf.modelRule m rr ps

rule-is-admissible
  : ∀ {R r}
  → R r
  → AdmissibleRule r R
rule-is-admissible rr = ByRule rr
