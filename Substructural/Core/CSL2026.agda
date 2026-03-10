open import Cubical.Core.Primitives

module Substructural.Core.CSL2026 {ℓ} (S : Type ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S
open import Substructural.Core.Derivation S
open import Substructural.Core.Nucleus S
open import Substructural.Core.Extensions S
open import Substructural.Core.Conservation S
open import Cubical.Data.List.Properties using (++-unit-r)

R'DerivableInMax : ∀ {j : S → S} {R R' : RuleSet} → Type ℓ
R'DerivableInMax {j} {R} {R'} = ∀ {r} → R' r → RuleHoldsIn r (Max⟨ j , R ⟩)

JHomogeneous : ∀ {j k : S → S} {R : RuleSet} → Type ℓ
JHomogeneous {j} {k} {R} =
  Nucleus k (Max⟨ j , R ⟩)
  × StableNucleus j (Lift1 k (L⟨ R ⟩))

A2026 : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
A2026 {j} {k} {R} {R'} = Max⟨ j , R ⟩ ⊆ Lift1 k (L⟨ R ∪R R' ⟩)

B2026 : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
B2026 {j} {k} {R} {R'} =
  ∀ {r} → (R ∪R R') r → RuleHoldsIn r (Lift1 k (L⟨ R ∪R R' ⟩))

C2026 : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
C2026 {j} {k} {R} {R'} = Kol1⟨ k , R ⟩ ⊆ L⟨ R ∪R R' ⟩

theorem6-statement : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
theorem6-statement {j} {k} {R} {R'} =
  (A2026 {j} {k} {R} {R'} ↔ B2026 {j} {k} {R} {R'})
  × (B2026 {j} {k} {R} {R'} ↔ C2026 {j} {k} {R} {R'})

lift1-all→
  : ∀ {k : S → S} {L : Entailment} {ps : List Seq}
  → PremisesHold (Lift1 k L) ps
  → PremisesHold L (map (mapBoth k) ps)
lift1-all→ {ps = []} []ᵃ = []ᵃ
lift1-all→ {k} {L} {ps = p ∷ ps} (d ∷ᵃ ds) = d ∷ᵃ lift1-all→ {k} {L} {ps} ds

lift1-all←
  : ∀ {k : S → S} {L : Entailment} {ps : List Seq}
  → PremisesHold L (map (mapBoth k) ps)
  → PremisesHold (Lift1 k L) ps
lift1-all← {ps = []} []ᵃ = []ᵃ
lift1-all← {k} {L} {ps = p ∷ ps} (d ∷ᵃ ds) = d ∷ᵃ lift1-all← {k} {L} {ps} ds

lift1-adm→mapBoth-adm
  : ∀ {k : S → S} {L : Entailment} {r : Rule}
  → RuleHoldsIn r (Lift1 k L)
  → RuleHoldsIn (mapBothRule k r) L
lift1-adm→mapBoth-adm {k} {L} {r} a =
  λ ds → a (lift1-all← {k} {L} {premises r} ds)

mapBoth-adm→lift1-adm
  : ∀ {k : S → S} {L : Entailment} {r : Rule}
  → RuleHoldsIn (mapBothRule k r) L
  → RuleHoldsIn r (Lift1 k L)
mapBoth-adm→lift1-adm {k} {L} {r} a =
  λ ds → a (lift1-all→ {k} {L} {premises r} ds)

lemma2-2026
  : ∀ {k : S → S} {R : RuleSet} {r : Rule}
  → R r
  → RuleHoldsIn r (Lift1 k (Kol1⟨ k , R ⟩))
lemma2-2026 {k} {R} {r} rr =
  mapBoth-adm→lift1-adm (embed-Rk1 {k} {R} {r} rr deriv-is-model)

max-in-R→R∪R'
  : ∀ {j : S → S} {R R' : RuleSet}
  → Max⟨ j , R ⟩ ⊆ Max⟨ j , R ∪R R' ⟩
max-in-R→R∪R' {j} {R} {R'} = lift-⊆R embed
  where
  embed : MaxRules j R ⊆R MaxRules j (R ∪R R')
  embed (inl rr) = inl (inl rr)
  embed (inr rest) = inr rest

jstab-in-Max
  : ∀ {j : S → S} {R : RuleSet} {a : S}
  → Max⟨ j , R ⟩ (singleton (j a)) a
jstab-in-Max {j} {R} {a} = embed-Lj+ {j} {R} {U = []} {V = []} {a = a} {b = a} Refl

destab-Max
  : ∀ {j : S → S} {R : RuleSet} {Γ : Ctx} {a : S}
  → Max⟨ j , R ⟩ Γ (j a)
  → Max⟨ j , R ⟩ Γ a
destab-Max {j} {R} {Γ} {a} d =
  transportCtx {L = Max⟨ j , R ⟩} {b = a} (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = j a} {b = a} d jstab-in-Max)

proposition5-2026
  : ∀ {j k : S → S} {R R' : RuleSet}
  → R'DerivableInMax {j} {R} {R'}
  → JHomogeneous {j} {k} {R}
  → (Max⟨ j , R ∪R R' ⟩ ⊆ Max⟨ j , R ⟩)
  → (Max⟨ j , R ⟩ ⊆ Max⟨ j , R ∪R R' ⟩)
  → JHomogeneous {j} {k} {R ∪R R'}
  → (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → (Kj j (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → (Max⟨ j , R ∪R R' ⟩ ⊆ Max⟨ j , R ⟩)
    × (Max⟨ j , R ⟩ ⊆ Max⟨ j , R ∪R R' ⟩)
    × JHomogeneous {j} {k} {R ∪R R'}
    × (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
    × (Kj j (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
proposition5-2026 {j} {k} {R} {R'} ρ hom max'⊆max max⊆max' hom' lift⊆max kj⊆max =
  max'⊆max
  , max⊆max'
  , hom'
  , lift⊆max
  , kj⊆max

transport-ruleHoldsIn
  : ∀ {r : Rule} {L L' : Entailment}
  → L ⊆ L'
  → L' ⊆ L
  → RuleHoldsIn r L
  → RuleHoldsIn r L'
transport-ruleHoldsIn to from a ds =
  to (a (premises-⊆ from ds))

a⇒b-2026
  : ∀ {j k : S → S} {R R' : RuleSet}
  → R'DerivableInMax {j} {R} {R'}
  → (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → A2026 {j} {k} {R} {R'}
  → B2026 {j} {k} {R} {R'}
a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max a {r} (inl rr0) =
  transport-ruleHoldsIn a lift⊆max
    (rule-is-derivable (inl rr0) deriv-is-model)
a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max a {r} (inr rr') =
  transport-ruleHoldsIn a lift⊆max
    (ρ rr')

b⇒a-2026
  : ∀ {j k : S → S} {R R' : RuleSet}
  → JHomogeneous {j} {k} {R ∪R R'}
  → (B2026 {j} {k} {R} {R'} → A2026 {j} {k} {R} {R'})
  → B2026 {j} {k} {R} {R'}
  → A2026 {j} {k} {R} {R'}
b⇒a-2026 hom b⇒a b = b⇒a b

theorem6
  : ∀ {j k : S → S} {R R' : RuleSet}
  → R'DerivableInMax {j} {R} {R'}
  → JHomogeneous {j} {k} {R ∪R R'}
  → (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → (B2026 {j} {k} {R} {R'} → A2026 {j} {k} {R} {R'})
  → (A2026 {j} {k} {R} {R'} → B2026 {j} {k} {R} {R'} → C2026 {j} {k} {R} {R'})
  → (C2026 {j} {k} {R} {R'} → A2026 {j} {k} {R} {R'})
  → theorem6-statement {j} {k} {R} {R'}
theorem6 {j} {k} {R} {R'} ρ hom' lift⊆max b⇒a ab⇒c c⇒a =
  intro (a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max) (b⇒a-2026 {j} {k} {R} {R'} hom' b⇒a)
  ,
  intro
    (λ b → ab⇒c (b⇒a-2026 {j} {k} {R} {R'} hom' b⇒a b) b)
    (λ c → a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max (c⇒a c))

theorem6-k=j-compatible
  : ∀ {j : S → S} {R R' : RuleSet}
  → Expansive j R
  → (M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩))
    ↔ (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩)
theorem6-k=j-compatible e = snd (snd (snd (theorem1 e)))
