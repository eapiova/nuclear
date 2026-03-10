module Substructural.FL.Basic where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula
open import Cubical.Data.List.Properties using (++-unit-r)

private
  variable
    R : RuleSet
    Γ U V W : Ctx
    a b c : Formula

lift-FL : ∀ {R} → FLRules ⊆R R → FL ⊆ Deriv R
lift-FL i = lift-⊆R i

mp⊸ : ∀ {a b} → FL (a ∷ (a `⊸ b) ∷ []) b
mp⊸ {a} {b} =
  ByRule (L⊸ {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b})
    (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

mp› : ∀ {a b} → FL ((b `› a) ∷ a ∷ []) b
mp› {a} {b} =
  ByRule (L› {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b})
    (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

mp⊸-in
  : ∀ {R a b}
  → FLRules ⊆R R
  → Deriv R (a ∷ (a `⊸ b) ∷ []) b
mp⊸-in i = lift-FL i mp⊸

mp›-in
  : ∀ {R a b}
  → FLRules ⊆R R
  → Deriv R ((b `› a) ∷ a ∷ []) b
mp›-in i = lift-FL i mp›

remark5-1-∧→·
  : ∀ {R a b}
  → FLRules ⊆R R
  → MonoRules ⊆R R
  → ContrRules ⊆R R
  → Deriv R (singleton (a `∧ b)) (a `· b)
remark5-1-∧→· {R} {a} {b} iFL iMono iContr =
  ByRule
    (iContr (contr-instance {U₁ = []} {U₂ = []} {a = a `∧ b} {b = a `· b}))
    (both ∷ᵃ []ᵃ)
  where
  da : Deriv R (singleton (a `∧ b)) a
  da =
    ByRule
      (iFL (L∧₁ {U = []} {V = []} {a = a} {b = b} {c = a}))
      (Refl ∷ᵃ []ᵃ)

  db : Deriv R (singleton (a `∧ b)) b
  db =
    ByRule
      (iFL (L∧₂ {U = []} {V = []} {a = a} {b = b} {c = b}))
      (Refl ∷ᵃ []ᵃ)

  both : Deriv R ((a `∧ b) ∷ (a `∧ b) ∷ []) (a `· b)
  both =
    ByRule
      (iFL (R· {U = singleton (a `∧ b)} {V = singleton (a `∧ b)} {a = a} {b = b}))
      (da ∷ᵃ db ∷ᵃ []ᵃ)

remark5-1-·→∧
  : ∀ {R a b}
  → FLRules ⊆R R
  → MonoRules ⊆R R
  → ContrRules ⊆R R
  → Deriv R (singleton (a `· b)) (a `∧ b)
remark5-1-·→∧ {R} {a} {b} iFL iMono iContr =
  ByRule
    (iFL (R∧ {U = singleton (a `· b)} {a = a} {b = b}))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
  where
  monoR : Mono (Deriv R)
  monoR = mono-from-rules iMono

  ab→a : Deriv R (a ∷ b ∷ []) a
  ab→a = monoR {U₁ = singleton a} {U₂ = []} {a = b} Refl

  ab→b : Deriv R (a ∷ b ∷ []) b
  ab→b = monoR {U₁ = []} {U₂ = singleton b} {a = a} Refl

  da : Deriv R (singleton (a `· b)) a
  da =
    ByRule
      (iFL (L· {U = []} {V = []} {a = a} {b = b} {c = a}))
      (ab→a ∷ᵃ []ᵃ)

  db : Deriv R (singleton (a `· b)) b
  db =
    ByRule
      (iFL (L· {U = []} {V = []} {a = a} {b = b} {c = b}))
      (ab→b ∷ᵃ []ᵃ)

remark5-2-⊸→›
  : ∀ {R a b}
  → FLRules ⊆R R
  → CommRules ⊆R R
  → Deriv R (singleton (a `⊸ b)) (b `› a)
remark5-2-⊸→› {R} {a} {b} iFL iComm =
  ByRule
    (iFL (R› {U = singleton (a `⊸ b)} {a = a} {b = b}))
    (swapped ∷ᵃ []ᵃ)
  where
  commR : Comm (Deriv R)
  commR = comm-from-rules iComm

  base : Deriv R (a ∷ (a `⊸ b) ∷ []) b
  base =
    ByRule
      (iFL (L⊸ {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  swapped : Deriv R ((a `⊸ b) ∷ a ∷ []) b
  swapped = commR {U₁ = []} {U₂ = []} {a₁ = a} {a₂ = a `⊸ b} {b = b} base

remark5-2-›→⊸
  : ∀ {R a b}
  → FLRules ⊆R R
  → CommRules ⊆R R
  → Deriv R (singleton (b `› a)) (a `⊸ b)
remark5-2-›→⊸ {R} {a} {b} iFL iComm =
  ByRule
    (iFL (R⊸ {U = singleton (b `› a)} {a = a} {b = b}))
    (swapped ∷ᵃ []ᵃ)
  where
  commR : Comm (Deriv R)
  commR = comm-from-rules iComm

  base : Deriv R ((b `› a) ∷ a ∷ []) b
  base =
    ByRule
      (iFL (L› {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  swapped : Deriv R (a ∷ (b `› a) ∷ []) b
  swapped = commR {U₁ = []} {U₂ = []} {a₁ = b `› a} {a₂ = a} {b = b} base

R∧-invert-left
  : ∀ {R Γ a b}
  → FLRules ⊆R R
  → Deriv R Γ (a `∧ b)
  → Deriv R Γ a
R∧-invert-left {R} {Γ} {a} {b} iFL d =
  transportCtx {L = Deriv R} (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} d
      (ByRule
        (iFL (L∧₁ {U = []} {V = []} {a = a} {b = b} {c = a}))
        (Refl ∷ᵃ []ᵃ)))

R∧-invert-right
  : ∀ {R Γ a b}
  → FLRules ⊆R R
  → Deriv R Γ (a `∧ b)
  → Deriv R Γ b
R∧-invert-right {R} {Γ} {a} {b} iFL d =
  transportCtx {L = Deriv R} (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} d
      (ByRule
        (iFL (L∧₂ {U = []} {V = []} {a = a} {b = b} {c = b}))
        (Refl ∷ᵃ []ᵃ)))

R⊸-invert
  : ∀ {R Γ a b}
  → FLRules ⊆R R
  → Deriv R Γ (a `⊸ b)
  → Deriv R (a ∷ Γ) b
R⊸-invert {R} {Γ} {a} {b} iFL d =
  transportCtx {L = Deriv R} (++-unit-r (a ∷ Γ))
    (Trans {U = Γ} {V₁ = singleton a} {V₂ = []} d (mp⊸-in iFL))

R›-invert
  : ∀ {R Γ a b}
  → FLRules ⊆R R
  → Deriv R Γ (b `› a)
  → Deriv R (Γ ++ (a ∷ [])) b
R›-invert {R} {Γ} {a} {b} iFL d =
  Trans {U = Γ} {V₁ = []} {V₂ = singleton a} d (mp›-in iFL)
