module Substructural.FL.Basic where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula using (Nucleus; nucleus-rj; nucleus-lj)
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula
open import Cubical.Data.List.Properties using (++-unit-r)

private
  variable
    j : Formula → Formula
    R : RuleSet
    Γ U V W : Ctx
    a b c : Formula

lift-FL : ∀ {R} → FLRules ⊆R R → FL ⊆ Deriv R
lift-FL i = lift-⊆R i

mp⊸ : ∀ {a b} → FL (a ∷ (a ⊸ b) ∷ []) b
mp⊸ {a} {b} =
  ByRule (L⊸ {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b})
    (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

mp› : ∀ {a b} → FL ((b › a) ∷ a ∷ []) b
mp› {a} {b} =
  ByRule (L› {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b})
    (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

mp⊸-in
  : ∀ {R a b}
  → FLRules ⊆R R
  → Deriv R (a ∷ (a ⊸ b) ∷ []) b
mp⊸-in i = lift-FL i mp⊸

mp›-in
  : ∀ {R a b}
  → FLRules ⊆R R
  → Deriv R ((b › a) ∷ a ∷ []) b
mp›-in i = lift-FL i mp›

remark4-1-∧→·
  : ∀ {R a b}
  → FLRules ⊆R R
  → MonoRules ⊆R R
  → ContrRules ⊆R R
  → Deriv R (singleton (a ∧ b)) (a · b)
remark4-1-∧→· {R} {a} {b} iFL iMono iContr =
  ByRule
    (iContr (contr-instance {U₁ = []} {U₂ = []} {a = a ∧ b} {b = a · b}))
    (both ∷ᵃ []ᵃ)
  where
  da : Deriv R (singleton (a ∧ b)) a
  da =
    ByRule
      (iFL (L∧₁ {U = []} {V = []} {a = a} {b = b} {c = a}))
      (Refl ∷ᵃ []ᵃ)

  db : Deriv R (singleton (a ∧ b)) b
  db =
    ByRule
      (iFL (L∧₂ {U = []} {V = []} {a = a} {b = b} {c = b}))
      (Refl ∷ᵃ []ᵃ)

  both : Deriv R ((a ∧ b) ∷ (a ∧ b) ∷ []) (a · b)
  both =
    ByRule
      (iFL (R· {U = singleton (a ∧ b)} {V = singleton (a ∧ b)} {a = a} {b = b}))
      (da ∷ᵃ db ∷ᵃ []ᵃ)

remark4-1-·→∧
  : ∀ {R a b}
  → FLRules ⊆R R
  → MonoRules ⊆R R
  → ContrRules ⊆R R
  → Deriv R (singleton (a · b)) (a ∧ b)
remark4-1-·→∧ {R} {a} {b} iFL iMono iContr =
  ByRule
    (iFL (R∧ {U = singleton (a · b)} {a = a} {b = b}))
    (da ∷ᵃ db ∷ᵃ []ᵃ)
  where
  monoR : Mono (Deriv R)
  monoR = mono-from-rules iMono

  ab→a : Deriv R (a ∷ b ∷ []) a
  ab→a = monoR {U₁ = singleton a} {U₂ = []} {a = b} Refl

  ab→b : Deriv R (a ∷ b ∷ []) b
  ab→b = monoR {U₁ = []} {U₂ = singleton b} {a = a} Refl

  da : Deriv R (singleton (a · b)) a
  da =
    ByRule
      (iFL (L· {U = []} {V = []} {a = a} {b = b} {c = a}))
      (ab→a ∷ᵃ []ᵃ)

  db : Deriv R (singleton (a · b)) b
  db =
    ByRule
      (iFL (L· {U = []} {V = []} {a = a} {b = b} {c = b}))
      (ab→b ∷ᵃ []ᵃ)

remark4-2-⊸→›
  : ∀ {R a b}
  → FLRules ⊆R R
  → CommRules ⊆R R
  → Deriv R (singleton (a ⊸ b)) (b › a)
remark4-2-⊸→› {R} {a} {b} iFL iComm =
  ByRule
    (iFL (R› {U = singleton (a ⊸ b)} {a = a} {b = b}))
    (swapped ∷ᵃ []ᵃ)
  where
  commR : Comm (Deriv R)
  commR = comm-from-rules iComm

  base : Deriv R (a ∷ (a ⊸ b) ∷ []) b
  base =
    ByRule
      (iFL (L⊸ {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  swapped : Deriv R ((a ⊸ b) ∷ a ∷ []) b
  swapped = commR {U₁ = []} {U₂ = []} {a₁ = a} {a₂ = a ⊸ b} {b = b} base

remark4-2-›→⊸
  : ∀ {R a b}
  → FLRules ⊆R R
  → CommRules ⊆R R
  → Deriv R (singleton (b › a)) (a ⊸ b)
remark4-2-›→⊸ {R} {a} {b} iFL iComm =
  ByRule
    (iFL (R⊸ {U = singleton (b › a)} {a = a} {b = b}))
    (swapped ∷ᵃ []ᵃ)
  where
  commR : Comm (Deriv R)
  commR = comm-from-rules iComm

  base : Deriv R ((b › a) ∷ a ∷ []) b
  base =
    ByRule
      (iFL (L› {U = singleton a} {V = []} {W = []} {a = a} {b = b} {c = b}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  swapped : Deriv R (a ∷ (b › a) ∷ []) b
  swapped = commR {U₁ = []} {U₂ = []} {a₁ = b › a} {a₂ = a} {b = b} base

R∧-invert-left
  : ∀ {R Γ a b}
  → FLRules ⊆R R
  → Deriv R Γ (a ∧ b)
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
  → Deriv R Γ (a ∧ b)
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
  → Deriv R Γ (a ⊸ b)
  → Deriv R (a ∷ Γ) b
R⊸-invert {R} {Γ} {a} {b} iFL d =
  transportCtx {L = Deriv R} (++-unit-r (a ∷ Γ))
    (Trans {U = Γ} {V₁ = singleton a} {V₂ = []} d (mp⊸-in iFL))

R›-invert
  : ∀ {R Γ a b}
  → FLRules ⊆R R
  → Deriv R Γ (b › a)
  → Deriv R (Γ ++ (a ∷ [])) b
R›-invert {R} {Γ} {a} {b} iFL d =
  Trans {U = Γ} {V₁ = []} {V₂ = singleton a} d (mp›-in iFL)

remark5
  : ∀ {j R}
  → FLRules ⊆R R
  → MonoRules ⊆R R
  → ContrRules ⊆R R
  → Nucleus j (Deriv R)
  → (∀ {a} → Deriv R (singleton a) (j a))
    × (∀ {a} → Deriv R (singleton (j a)) (j (j a))
              × Deriv R (singleton (j (j a))) (j a))
    × (∀ {a b} → Deriv R (singleton (j (a · b))) (j a · j b)
                × Deriv R (singleton (j a · j b)) (j (a · b)))
remark5 {j} {R} iFL iMono iContr n =
  cond1
  ,
  cond2
  ,
  cond3
  where
  rj : ∀ {Γ a} → Deriv R Γ a → Deriv R Γ (j a)
  rj = nucleus-rj n

  lj : ∀ {U V a b} → Deriv R ⊢ U ++ a ∷ V ▷ j b → Deriv R ⊢ U ++ j a ∷ V ▷ j b
  lj = nucleus-lj n

  monoR : Mono (Deriv R)
  monoR = mono-from-rules iMono

  contrR : Contr (Deriv R)
  contrR = contr-from-rules iContr

  cond1 : ∀ {a} → Deriv R (singleton a) (j a)
  cond1 = rj Refl

  cond2
    : ∀ {a}
    → Deriv R (singleton (j a)) (j (j a))
      × Deriv R (singleton (j (j a))) (j a)
  cond2 {a} =
    rj Refl
    ,
    lj {U = []} {V = []} {a = j a} {b = a} Refl

  cond3
    : ∀ {a b}
    → Deriv R (singleton (j (a · b))) (j a · j b)
      × Deriv R (singleton (j a · j b)) (j (a · b))
  cond3 {a} {b} =
    j·→j·
    ,
    j·-shift
    where
    ab→a : Deriv R (a ∷ b ∷ []) a
    ab→a = monoR {U₁ = singleton a} {U₂ = []} {a = b} Refl

    ab→b : Deriv R (a ∷ b ∷ []) b
    ab→b = monoR {U₁ = []} {U₂ = singleton b} {a = a} Refl

    ·→a : Deriv R (singleton (a · b)) a
    ·→a =
      ByRule
        (iFL (L· {U = []} {V = []} {a = a} {b = b} {c = a}))
        (ab→a ∷ᵃ []ᵃ)

    ·→b : Deriv R (singleton (a · b)) b
    ·→b =
      ByRule
        (iFL (L· {U = []} {V = []} {a = a} {b = b} {c = b}))
        (ab→b ∷ᵃ []ᵃ)

    ·→ja : Deriv R (singleton (a · b)) (j a)
    ·→ja = rj ·→a

    ·→jb : Deriv R (singleton (a · b)) (j b)
    ·→jb = rj ·→b

    j·→ja : Deriv R (singleton (j (a · b))) (j a)
    j·→ja = lj {U = []} {V = []} {a = a · b} {b = a} ·→ja

    j·→jb : Deriv R (singleton (j (a · b))) (j b)
    j·→jb = lj {U = []} {V = []} {a = a · b} {b = b} ·→jb

    j·j·→j·j
      : Deriv R (j (a · b) ∷ j (a · b) ∷ []) (j a · j b)
    j·j·→j·j =
      ByRule
        (iFL
          (R·
            {U = singleton (j (a · b))}
            {V = singleton (j (a · b))}
            {a = j a}
            {b = j b}))
        (j·→ja ∷ᵃ j·→jb ∷ᵃ []ᵃ)

    j·→j· : Deriv R (singleton (j (a · b))) (j a · j b)
    j·→j· =
      contrR {U₁ = []} {U₂ = []} {a = j (a · b)} {b = j a · j b} j·j·→j·j

    a,b→j· : Deriv R (a ∷ b ∷ []) (j (a · b))
    a,b→j· =
      rj
        (ByRule
          (iFL (R· {U = singleton a} {V = singleton b} {a = a} {b = b}))
          (Refl ∷ᵃ Refl ∷ᵃ []ᵃ))

    a,jb→j· : Deriv R (a ∷ j b ∷ []) (j (a · b))
    a,jb→j· = lj {U = singleton a} {V = []} {a = b} {b = a · b} a,b→j·

    ja,jb→j· : Deriv R (j a ∷ j b ∷ []) (j (a · b))
    ja,jb→j· = lj {U = []} {V = singleton (j b)} {a = a} {b = a · b} a,jb→j·

    j·-shift : Deriv R (singleton (j a · j b)) (j (a · b))
    j·-shift =
      ByRule
        (iFL (L· {U = []} {V = []} {a = j a} {b = j b} {c = j (a · b)}))
        (ja,jb→j· ∷ᵃ []ᵃ)
