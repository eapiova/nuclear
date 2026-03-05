module Substructural.FL.Glivenko where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.FL.Basic
open import Substructural.FL.Shifts
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula using (transportCtx)
open import Cubical.Data.List.Properties using (++-unit-r)

private
  variable
    Γ : Ctx
    a b : Formula

gL : Formula → Formula
gL a = `∼ (`− a)

gR : Formula → Formula
gR a = `− (`∼ a)

¬_ : Formula → Formula
¬ a = a `⊸ `0

¬¬_ : Formula → Formula
¬¬ a = ¬ (¬ a)

nn : Formula → Formula
nn = ¬¬_

InFLe : Entailment
InFLe = M⟨ nn , FLeRules ⟩

Cla : Entailment
Cla = M⟨ nn , MinRules ⟩

Gli : Entailment
Gli = G⟨ nn , MinRules ⟩

RgL : Rj gL FL
RgL {Γ} {a} d =
  ByRule (R⊸ {U = Γ} {a = `− a} {b = `0}) (d0 ∷ᵃ []ᵃ)
  where
  d0 : FL (`− a ∷ Γ) `0
  d0 = transportCtx {L = FL} (cong ((`− a) ∷_) (++-unit-r Γ)) d0'
    where
    d0' : FL (`− a ∷ (Γ ++ [])) `0
    d0' =
      ByRule
        (L› {U = Γ} {V = []} {W = []} {a = a} {b = `0} {c = `0})
        (d ∷ᵃ Refl ∷ᵃ []ᵃ)

LgL-left : Ljleft gL FL
LgL-left {U} {a} {b} d =
  ByRule (R⊸ {U = suffix U (gL a)} {a = `− b} {b = `0}) (d3 ∷ᵃ []ᵃ)
  where
  mp-gLb : FL (`− b ∷ gL b ∷ []) `0
  mp-gLb =
    ByRule
      (L⊸ {U = singleton (`− b)} {V = []} {W = []} {a = `− b} {b = `0} {c = `0})
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  d1 : FL (`− b ∷ suffix U a) `0
  d1 = transportCtx {L = FL} (++-unit-r (`− b ∷ suffix U a)) d1'
    where
    d1' : FL (plug (singleton (`− b)) [] (suffix U a)) `0
    d1' = Trans {U = suffix U a} {V₁ = singleton (`− b)} {V₂ = []} d mp-gLb

  d2 : FL (`− b ∷ U) (`− a)
  d2 = ByRule (R› {U = `− b ∷ U} {a = a} {b = `0}) (d1 ∷ᵃ []ᵃ)

  d3 : FL (`− b ∷ suffix U (gL a)) `0
  d3 =
    ByRule
      (L⊸ {U = `− b ∷ U} {V = []} {W = []} {a = `− a} {b = `0} {c = `0})
      (d2 ∷ᵃ Refl ∷ᵃ []ᵃ)

RgR : Rj gR FL
RgR {Γ} {a} d =
  ByRule (R› {U = Γ} {a = a `⊸ `0} {b = `0}) (d0 ∷ᵃ []ᵃ)
  where
  d0 : FL (Γ ++ (a `⊸ `0) ∷ []) `0
  d0 =
    ByRule
      (L⊸ {U = Γ} {V = []} {W = []} {a = a} {b = `0} {c = `0})
      (d ∷ᵃ Refl ∷ᵃ []ᵃ)

LgR-right : Ljright gR FL
LgR-right {U} {a} {b} d =
  ByRule (R› {U = gR a ∷ U} {a = b `⊸ `0} {b = `0}) (d3 ∷ᵃ []ᵃ)
  where
  mp-gRb : FL (gR b ∷ (b `⊸ `0) ∷ []) `0
  mp-gRb =
    ByRule
      (L› {U = singleton (b `⊸ `0)} {V = []} {W = []} {a = b `⊸ `0} {b = `0} {c = `0})
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  d1 : FL (prefix a (U ++ (b `⊸ `0) ∷ [])) `0
  d1 = Trans {U = prefix a U} {V₁ = []} {V₂ = singleton (b `⊸ `0)} d mp-gRb

  d2 : FL (U ++ (b `⊸ `0) ∷ []) (a `⊸ `0)
  d2 = ByRule (R⊸ {U = U ++ (b `⊸ `0) ∷ []} {a = a} {b = `0}) (d1 ∷ᵃ []ᵃ)

  d3 : FL (gR a ∷ U ++ (b `⊸ `0) ∷ []) `0
  d3 = transportCtx {L = FL} p d3'
    where
    p : gR a ∷ ((U ++ (b `⊸ `0) ∷ []) ++ []) ≡ gR a ∷ U ++ (b `⊸ `0) ∷ []
    p = cong ((gR a) ∷_) (++-unit-r (U ++ (b `⊸ `0) ∷ []))

    d3' : FL (gR a ∷ ((U ++ (b `⊸ `0) ∷ []) ++ [])) `0
    d3' =
      ByRule
        (L›
          {U = U ++ (b `⊸ `0) ∷ []}
          {V = []}
          {W = []}
          {a = a `⊸ `0}
          {b = `0}
          {c = `0})
        (d2 ∷ᵃ Refl ∷ᵃ []ᵃ)

proposition20 : LeftNucleus gL FL × RightNucleus gR FL
proposition20 =
  mkLeftNucleus RgL LgL-left
  ,
  mkRightNucleus RgR LgR-right

GL-Cond1 : Entailment → Type
GL-Cond1 L = ∀ {Γ a} → M⟨ gL , FLRules ⟩ Γ a ↔ L Γ (gL a)

GL-Cond2 : Entailment → Type
GL-Cond2 L = G⟨ gL , FLRules ⟩ ⊆ L

GL-Cond3 : Entailment → Type
GL-Cond3 L =
  (∀ {a b} → L (singleton (gL a `∧ gL b)) (gL (a `∧ b)))
  × (∀ {a b} → L (singleton (a `⊸ gL b)) (gL (a `⊸ b)))
  × (∀ {a b} → L (singleton (gL b `› a)) (gL (b `› a)))

GR-Cond1 : Entailment → Type
GR-Cond1 L = ∀ {Γ a} → M⟨ gR , FLRules ⟩ Γ a ↔ L Γ (gR a)

GR-Cond2 : Entailment → Type
GR-Cond2 L = G⟨ gR , FLRules ⟩ ⊆ L

GR-Cond3 : Entailment → Type
GR-Cond3 L =
  (∀ {a b} → L (singleton (gR a `∧ gR b)) (gR (a `∧ b)))
  × (∀ {a b} → L (singleton (a `⊸ gR b)) (gR (a `⊸ b)))
  × (∀ {a b} → L (singleton (gR b `› a)) (gR (b `› a)))

theorem21 : (L : Entailment) → Type
theorem21 L =
  (L ⊆ M⟨ gL , FLRules ⟩
  → (GL-Cond1 L ↔ GL-Cond2 L)
    × (GL-Cond2 L ↔ GL-Cond3 L))
  ×
  (L ⊆ M⟨ gR , FLRules ⟩
  → (GR-Cond1 L ↔ GR-Cond2 L)
    × (GR-Cond2 L ↔ GR-Cond3 L))

gl-cond3-full→paper
  : ∀ {L}
  → Theorem19-Cond3 gL L
  → GL-Cond3 L
gl-cond3-full→paper (_ , s∧ , s⊸ , s›) = s∧ , s⊸ , s›

gl-cond3-paper→full
  : ∀ {L}
  → Shift· gL L
  → GL-Cond3 L
  → Theorem19-Cond3 gL L
gl-cond3-paper→full s· (s∧ , s⊸ , s›) = s· , s∧ , s⊸ , s›

gr-cond3-full→paper
  : ∀ {L}
  → Theorem19-Cond3 gR L
  → GR-Cond3 L
gr-cond3-full→paper (_ , s∧ , s⊸ , s›) = s∧ , s⊸ , s›

gr-cond3-paper→full
  : ∀ {L}
  → Shift· gR L
  → GR-Cond3 L
  → Theorem19-Cond3 gR L
gr-cond3-paper→full s· (s∧ , s⊸ , s›) = s· , s∧ , s⊸ , s›

theorem21-from-theorem19
  : (L : Entailment)
  → theorem19 gL L
  → theorem19 gR L
  → Shift· gL L
  → Shift· gR L
  → theorem21 L
theorem21-from-theorem19 L t19L t19R s·L s·R =
  leftPart
  ,
  rightPart
  where
  ln-gL : LeftNucleus gL FL
  ln-gL = fst proposition20

  rn-gR : RightNucleus gR FL
  rn-gR = snd proposition20

  leftPart
    : L ⊆ M⟨ gL , FLRules ⟩
    → (GL-Cond1 L ↔ GL-Cond2 L)
      × (GL-Cond2 L ↔ GL-Cond3 L)
  leftPart l⊆m =
    eq12
    ,
    intro to23 from23
    where
    t : (Theorem19-Cond1 gL L ↔ Theorem19-Cond2 gL L)
        × (Theorem19-Cond2 gL L ↔ Theorem19-Cond3 gL L)
    t = t19L (inj₂ (inj₁ ln-gL)) l⊆m

    eq12 : GL-Cond1 L ↔ GL-Cond2 L
    eq12 = fst t

    eq23full : GL-Cond2 L ↔ Theorem19-Cond3 gL L
    eq23full = snd t

    to23 : GL-Cond2 L → GL-Cond3 L
    to23 c2 = gl-cond3-full→paper {L = L} (to eq23full c2)

    from23 : GL-Cond3 L → GL-Cond2 L
    from23 c3 = from eq23full (gl-cond3-paper→full {L = L} s·L c3)

  rightPart
    : L ⊆ M⟨ gR , FLRules ⟩
    → (GR-Cond1 L ↔ GR-Cond2 L)
      × (GR-Cond2 L ↔ GR-Cond3 L)
  rightPart l⊆m =
    eq12
    ,
    intro to23 from23
    where
    t : (Theorem19-Cond1 gR L ↔ Theorem19-Cond2 gR L)
        × (Theorem19-Cond2 gR L ↔ Theorem19-Cond3 gR L)
    t = t19R (inj₁ rn-gR) l⊆m

    eq12 : GR-Cond1 L ↔ GR-Cond2 L
    eq12 = fst t

    eq23full : GR-Cond2 L ↔ Theorem19-Cond3 gR L
    eq23full = snd t

    to23 : GR-Cond2 L → GR-Cond3 L
    to23 c2 = gr-cond3-full→paper {L = L} (to eq23full c2)

    from23 : GR-Cond3 L → GR-Cond2 L
    from23 c3 = from eq23full (gr-cond3-paper→full {L = L} s·R c3)

Ono-Cond1 : Entailment → Type
Ono-Cond1 L = ∀ {Γ a} → InFLe Γ a ↔ L Γ (¬¬ a)

Ono-Cond2 : Entailment → Type
Ono-Cond2 L = G⟨ nn , FLeRules ⟩ ⊆ L

Ono-Cond3 : Entailment → Type
Ono-Cond3 L =
  (∀ {a b} → L (singleton ((¬¬ a) `∧ (¬¬ b))) (¬¬ (a `∧ b)))
  × (∀ {a b} → L (singleton (a `⊸ (¬¬ b))) (¬¬ (a `⊸ b)))

Odintsov-Cond1 : Entailment → Type
Odintsov-Cond1 L = ∀ {Γ a} → Cla Γ a ↔ L Γ (¬¬ a)

Odintsov-Cond2 : Entailment → Type
Odintsov-Cond2 L = Gli ⊆ L

Odintsov-Cond3 : Entailment → Type
Odintsov-Cond3 L = ∀ {a b} → L (singleton (a `⊸ (¬¬ b))) (¬¬ (a `⊸ b))

Glivenko-Cond : Type
Glivenko-Cond = ∀ {Γ a} → Cla Γ a ↔ Int Γ (¬¬ a)

corollary22 : Type₁
corollary22 =
  (∀ (L : Entailment)
   → FLe ⊆ L
   → L ⊆ InFLe
   → (Ono-Cond1 L ↔ Ono-Cond2 L)
     × (Ono-Cond2 L ↔ Ono-Cond3 L))
  ×
  (∀ (L : Entailment)
   → Min ⊆ L
   → L ⊆ Cla
   → (Odintsov-Cond1 L ↔ Odintsov-Cond2 L)
     × (Odintsov-Cond2 L ↔ Odintsov-Cond3 L))
  ×
  Glivenko-Cond
