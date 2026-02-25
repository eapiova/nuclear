{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Extensions {ℓ} (S : Set ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S
open import Substructural.Core.Derivation S
open import Substructural.Core.Nucleus S
open import Cubical.Data.List.Properties using (++-unit-r)

-- Definition 7(1): Kleisli j-extension.
Kj : (S → S) → Entailment → Entailment
Kj j L Γ a = L Γ (j a)

Lift1 : (S → S) → Entailment → Entailment
Lift1 k L Γ a = L (mapCtx k Γ) (k a)

-- Definition 7(2): Lj rule family added to Gj.
data LjRules (j : S → S) : RuleSet where
  lj-instance
    : ∀ {U V a b}
    → LjRules j (mkRule ((plug₁ U a V ▷ j b) ∷ []) (plug₁ U (j a) V ▷ j b))

data Lj+Rules (j : S → S) : RuleSet where
  lj+-instance
    : ∀ {U V a b}
    → Lj+Rules j (mkRule ((plug₁ U a V ▷ b) ∷ []) (plug₁ U (j a) V ▷ b))

-- Definition 7(3): j-stab rule family added to Mj.
data JStabRules (j : S → S) : RuleSet where
  jstab-instance
    : ∀ {a}
    → JStabRules j (mkRule [] (singleton (j a) ▷ a))

data ExpRules (j : S → S) : RuleSet where
  exp-instance
    : ∀ {a}
    → ExpRules j (mkRule [] (singleton a ▷ j a))

-- Definition 7(2): rj-images of base rules.
data RjRules (j : S → S) (R : RuleSet) : RuleSet where
  rj-instance
    : ∀ {r}
    → R r
    → RjRules j R (rj j r)

data Rk1Rules (k : S → S) (R : RuleSet) : RuleSet where
  rk1-instance
    : ∀ {r}
    → R r
    → Rk1Rules k R (mapBothRule k r)

data LkMinusRules (k : S → S) : RuleSet where
  lkminus-instance
    : ∀ {U V a b}
    → LkMinusRules k (mkRule ((plug₁ U (k a) V ▷ b) ∷ []) (plug₁ U (k (k a)) V ▷ b))

data RkMinusRules (k : S → S) : RuleSet where
  rkminus-instance
    : ∀ {Γ a}
    → RkMinusRules k (mkRule ((Γ ▷ k a) ∷ []) (Γ ▷ k (k a)))

data CommRules : RuleSet where
  comm-instance
    : ∀ {U₁ U₂ a₁ a₂ b}
    → CommRules
        (mkRule
          ((U₁ ++ (a₁ ∷ a₂ ∷ U₂) ▷ b) ∷ [])
          (U₁ ++ (a₂ ∷ a₁ ∷ U₂) ▷ b))

data MonoRules : RuleSet where
  mono-instance
    : ∀ {U₁ U₂ a b}
    → MonoRules
        (mkRule
          ((U₁ ++ U₂ ▷ b) ∷ [])
          (plug₁ U₁ a U₂ ▷ b))

data ContrRules : RuleSet where
  contr-instance
    : ∀ {U₁ U₂ a b}
    → ContrRules
        (mkRule
          ((U₁ ++ (a ∷ a ∷ U₂) ▷ b) ∷ [])
          (plug₁ U₁ a U₂ ▷ b))

-- Definition 7(2): Gj(L) = L + {Lj} + {rj : r ∈ R}. Expansive or not?
GjRules : (S → S) → RuleSet → RuleSet
GjRules j R r = R r ⊎ (LjRules j r ⊎ RjRules j R r)

-- Definition 7(3): Mj(L) = L + {j-stab}.
MjRules : (S → S) → RuleSet → RuleSet
MjRules j R r = R r ⊎ JStabRules j r

MaxRules : (S → S) → RuleSet → RuleSet
MaxRules j R r = R r ⊎ (Lj+Rules j r ⊎ ExpRules j r)

Kol1Rules : (S → S) → RuleSet → RuleSet
Kol1Rules k R r = R r ⊎ (Rk1Rules k R r ⊎ (LkMinusRules k r ⊎ RkMinusRules k r))

L⟨_⟩ : RuleSet → Entailment
L⟨ R ⟩ = Deriv R

G⟨_,_⟩ : (S → S) → RuleSet → Entailment
G⟨ j , R ⟩ = Deriv (GjRules j R)

M⟨_,_⟩ : (S → S) → RuleSet → Entailment
M⟨ j , R ⟩ = Deriv (MjRules j R)

Max⟨_,_⟩ : (S → S) → RuleSet → Entailment
Max⟨ j , R ⟩ = Deriv (MaxRules j R)

Kol1⟨_,_⟩ : (S → S) → RuleSet → Entailment
Kol1⟨ k , R ⟩ = Deriv (Kol1Rules k R)

infixr 5 _+_

_+_ : RuleSet → RuleSet → Entailment
R + R' = Deriv (R ∪R R')

embed-Lj
  : ∀ {j R U V a b}
  → G⟨ j , R ⟩ (plug₁ U a V) (j b)
  → G⟨ j , R ⟩ (plug₁ U (j a) V) (j b)
embed-Lj d = ByRule (inj₂ (inj₁ lj-instance)) (d ∷ᵃ []ᵃ)

embed-Lj+
  : ∀ {j R U V a b}
  → Max⟨ j , R ⟩ (plug₁ U a V) b
  → Max⟨ j , R ⟩ (plug₁ U (j a) V) b
embed-Lj+ d = ByRule (inj₂ (inj₁ lj+-instance)) (d ∷ᵃ []ᵃ)

embed-Exp
  : ∀ {j R a}
  → Max⟨ j , R ⟩ (singleton a) (j a)
embed-Exp = ByRule (inj₂ (inj₂ exp-instance)) []ᵃ

embed-jstab
  : ∀ {j R a}
  → M⟨ j , R ⟩ (singleton (j a)) a
embed-jstab = ByRule (inj₂ jstab-instance) []ᵃ

jstab-in-M
  : ∀ {j R a}
  → M⟨ j , R ⟩ (singleton (j a)) a
jstab-in-M = embed-jstab

lift-base-into-G
  : ∀ {j R}
  → L⟨ R ⟩ ⊆ G⟨ j , R ⟩
lift-base-into-G = lift-⊆R (inj₁)

lift-base-into-M
  : ∀ {j R}
  → L⟨ R ⟩ ⊆ M⟨ j , R ⟩
lift-base-into-M = lift-⊆R (inj₁)

lift-base-into-Max
  : ∀ {j R}
  → L⟨ R ⟩ ⊆ Max⟨ j , R ⟩
lift-base-into-Max = lift-⊆R (inj₁)

lift-base-into-Kol1
  : ∀ {k R}
  → L⟨ R ⟩ ⊆ Kol1⟨ k , R ⟩
lift-base-into-Kol1 = lift-⊆R (inj₁)

embed-Rk1
  : ∀ {k R r}
  → R r
  → DerivableRule (mapBothRule k r) (Kol1⟨ k , R ⟩)
embed-Rk1 rr = mkDerivableRule λ ds → ByRule (inj₂ (inj₁ (rk1-instance rr))) ds

embed-Lk-
  : ∀ {k R U V a b}
  → Kol1⟨ k , R ⟩ (plug₁ U (k a) V) b
  → Kol1⟨ k , R ⟩ (plug₁ U (k (k a)) V) b
embed-Lk- d = ByRule (inj₂ (inj₂ (inj₁ lkminus-instance))) (d ∷ᵃ []ᵃ)

embed-Rk-
  : ∀ {k R Γ a}
  → Kol1⟨ k , R ⟩ Γ (k a)
  → Kol1⟨ k , R ⟩ Γ (k (k a))
embed-Rk- d = ByRule (inj₂ (inj₂ (inj₂ rkminus-instance))) (d ∷ᵃ []ᵃ)

GjRules-monotone
  : ∀ {j R R'}
  → R ⊆R R'
  → GjRules j R ⊆R GjRules j R'
GjRules-monotone i (inl rr) = inl (i rr)
GjRules-monotone i (inr (inl lj)) = inr (inl lj)
GjRules-monotone i (inr (inr (rj-instance rr))) = inr (inr (rj-instance (i rr)))

MjRules-monotone
  : ∀ {j R R'}
  → R ⊆R R'
  → MjRules j R ⊆R MjRules j R'
MjRules-monotone i (inl rr) = inl (i rr)
MjRules-monotone i (inr js) = inr js

lift-G
  : ∀ {j R R'}
  → R ⊆R R'
  → G⟨ j , R ⟩ ⊆ G⟨ j , R' ⟩
lift-G {j} {R} {R'} i = lift-⊆R (GjRules-monotone {j} {R} {R'} i)

lift-M
  : ∀ {j R R'}
  → R ⊆R R'
  → M⟨ j , R ⟩ ⊆ M⟨ j , R' ⟩
lift-M {j} {R} {R'} i = lift-⊆R (MjRules-monotone {j} {R} {R'} i)

-- Lemma 8(2): j is a bi-nucleus over Gj(L).
bi-on-G
  : ∀ {j R}
  → BiNucleus j (G⟨ j , R ⟩)
bi-on-G = mkBiNucleus embed-Lj

-- Lemma 8(2): j is a bi-nucleus over Mj(L).
bi-on-M
  : ∀ {j R}
  → BiNucleus j (M⟨ j , R ⟩)
bi-on-M = mkBiNucleus liftLj
  where
  liftLj
    : ∀ {j R U V a b}
    → M⟨ j , R ⟩ (plug₁ U a V) (j b)
    → M⟨ j , R ⟩ (plug₁ U (j a) V) (j b)
  liftLj {j} {R} {U} {V} {a} {b} d =
    Trans {U = singleton (j a)} {V₁ = U} {V₂ = V} embed-jstab d

destab-M
  : ∀ {j R Γ a}
  → M⟨ j , R ⟩ Γ (j a)
  → M⟨ j , R ⟩ Γ a
destab-M {j} {R} {Γ} {a} d =
  subst (λ X → M⟨ j , R ⟩ X a) (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = j a} {b = a} d embed-jstab)

raise-M-from-expansiveR
  : ∀ {j R Γ a}
  → ExpansiveR j R
  → M⟨ j , R ⟩ Γ a
  → M⟨ j , R ⟩ Γ (j a)
raise-M-from-expansiveR {j} {R} e =
  lift-ExpansiveR e (λ rr → inl rr)
