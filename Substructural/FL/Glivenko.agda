module Substructural.FL.Glivenko where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.FL.Rules
open import Substructural.FL.Basic
open import Substructural.FL.Shifts
open import Substructural.FL.Theorem19
open import Substructural.FL.DoubleNegation
open import Substructural.FL.Lemma17
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Nucleus Formula
open import Substructural.Core.Extensions Formula
open import Substructural.Core.Conservation Formula
  using
    ( Mono
    ; Contr
    ; transportCtx
    ; comm-from-rules
    ; mono-from-rules
    ; contr-from-rules
    ; g⊆m
    ; m→gj
    ; jstab→lj+
    ; destab-mapSuccAll
    )
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

RgL-R : ∀ {R'} → FLRules ⊆R R' → Rj gL (Deriv R')
RgL-R iFL {Γ} {a} d =
  ByRule (iFL (R⊸ {U = Γ} {a = `− a} {b = `0})) (d0 ∷ᵃ []ᵃ)
  where
  d0 : Deriv _ (`− a ∷ Γ) `0
  d0 = transportCtx {L = Deriv _} (cong ((`− a) ∷_) (++-unit-r Γ)) d0'
    where
    d0' : Deriv _ (`− a ∷ (Γ ++ [])) `0
    d0' =
      ByRule
        (iFL (L› {U = Γ} {V = []} {W = []} {a = a} {b = `0} {c = `0}))
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

LgL-left-R : ∀ {R'} → FLRules ⊆R R' → Ljleft gL (Deriv R')
LgL-left-R iFL {U} {a} {b} d =
  ByRule (iFL (R⊸ {U = suffix U (gL a)} {a = `− b} {b = `0})) (d3 ∷ᵃ []ᵃ)
  where
  mp-gLb : Deriv _ (`− b ∷ gL b ∷ []) `0
  mp-gLb =
    ByRule
      (iFL (L⊸ {U = singleton (`− b)} {V = []} {W = []} {a = `− b} {b = `0} {c = `0}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  d1 : Deriv _ (`− b ∷ suffix U a) `0
  d1 = transportCtx {L = Deriv _} (++-unit-r (`− b ∷ suffix U a)) d1'
    where
    d1' : Deriv _ (plug (singleton (`− b)) [] (suffix U a)) `0
    d1' = Trans {U = suffix U a} {V₁ = singleton (`− b)} {V₂ = []} d mp-gLb

  d2 : Deriv _ (`− b ∷ U) (`− a)
  d2 = ByRule (iFL (R› {U = `− b ∷ U} {a = a} {b = `0})) (d1 ∷ᵃ []ᵃ)

  d3 : Deriv _ (`− b ∷ suffix U (gL a)) `0
  d3 =
    ByRule
      (iFL (L⊸ {U = `− b ∷ U} {V = []} {W = []} {a = `− a} {b = `0} {c = `0}))
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

RgR-R : ∀ {R'} → FLRules ⊆R R' → Rj gR (Deriv R')
RgR-R iFL {Γ} {a} d =
  ByRule (iFL (R› {U = Γ} {a = a `⊸ `0} {b = `0})) (d0 ∷ᵃ []ᵃ)
  where
  d0 : Deriv _ (Γ ++ (a `⊸ `0) ∷ []) `0
  d0 =
    ByRule
      (iFL (L⊸ {U = Γ} {V = []} {W = []} {a = a} {b = `0} {c = `0}))
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

LgR-right-R : ∀ {R'} → FLRules ⊆R R' → Ljright gR (Deriv R')
LgR-right-R iFL {U} {a} {b} d =
  ByRule (iFL (R› {U = gR a ∷ U} {a = b `⊸ `0} {b = `0})) (d3 ∷ᵃ []ᵃ)
  where
  mp-gRb : Deriv _ (gR b ∷ (b `⊸ `0) ∷ []) `0
  mp-gRb =
    ByRule
      (iFL (L› {U = singleton (b `⊸ `0)} {V = []} {W = []} {a = b `⊸ `0} {b = `0} {c = `0}))
      (Refl ∷ᵃ Refl ∷ᵃ []ᵃ)

  d1 : Deriv _ (prefix a (U ++ (b `⊸ `0) ∷ [])) `0
  d1 = Trans {U = prefix a U} {V₁ = []} {V₂ = singleton (b `⊸ `0)} d mp-gRb

  d2 : Deriv _ (U ++ (b `⊸ `0) ∷ []) (a `⊸ `0)
  d2 = ByRule (iFL (R⊸ {U = U ++ (b `⊸ `0) ∷ []} {a = a} {b = `0})) (d1 ∷ᵃ []ᵃ)

  d3 : Deriv _ (gR a ∷ U ++ (b `⊸ `0) ∷ []) `0
  d3 = transportCtx {L = Deriv _} p d3'
    where
    p : gR a ∷ ((U ++ (b `⊸ `0) ∷ []) ++ []) ≡ gR a ∷ U ++ (b `⊸ `0) ∷ []
    p = cong ((gR a) ∷_) (++-unit-r (U ++ (b `⊸ `0) ∷ []))

    d3' : Deriv _ (gR a ∷ ((U ++ (b `⊸ `0) ∷ []) ++ [])) `0
    d3' =
      ByRule
        (iFL
          (L›
            {U = U ++ (b `⊸ `0) ∷ []}
            {V = []}
            {W = []}
            {a = a `⊸ `0}
            {b = `0}
            {c = `0}))
        (d2 ∷ᵃ Refl ∷ᵃ []ᵃ)

remark6 : LeftNucleus gL FL × RightNucleus gR FL
remark6 =
  mkLeftNucleus RgL LgL-left
  ,
  mkRightNucleus RgR LgR-right

gL-expansive : Expansive gL FLRules
gL-expansive = mkExpansive (RgL-R (λ r → r))

gL-leftProgressiveR : LeftProgressiveR gL FLRules
gL-leftProgressiveR = mkLeftProgressiveR LgL-left-R

gR-expansive : Expansive gR FLRules
gR-expansive = mkExpansive (RgR-R (λ r → r))

gR-rightProgressiveR : RightProgressiveR gR FLRules
gR-rightProgressiveR = mkRightProgressiveR LgR-right-R

gL-t3 : ∀ {R} → FLRules ⊆R R → theorem3 gL (Deriv R)
gL-t3 iFL _ l⊆m = theorem3-proof iFL gL-expansive (inl gL-leftProgressiveR) l⊆m

gR-t3 : ∀ {R} → FLRules ⊆R R → theorem3 gR (Deriv R)
gR-t3 iFL _ l⊆m = theorem3-proof iFL gR-expansive (inr (inl gR-rightProgressiveR)) l⊆m

GL-Cond1 : Entailment → Type
GL-Cond1 L = ∀ {Γ a} → M⟨ gL , FLRules ⟩ Γ a ↔ L Γ (gL a)

GL-Cond2 : Entailment → Type
GL-Cond2 L = G⟨ gL , FLRules ⟩ ⊆ L

GL-Cond3 : Entailment → Type
GL-Cond3 = Theorem3-Cond3 gL

GR-Cond1 : Entailment → Type
GR-Cond1 L = ∀ {Γ a} → M⟨ gR , FLRules ⟩ Γ a ↔ L Γ (gR a)

GR-Cond2 : Entailment → Type
GR-Cond2 L = G⟨ gR , FLRules ⟩ ⊆ L

GR-Cond3 : Entailment → Type
GR-Cond3 = Theorem3-Cond3 gR

corollary1 : (L : Entailment) → Type
corollary1 L =
  (L ⊆ M⟨ gL , FLRules ⟩
  → (GL-Cond1 L ↔ GL-Cond2 L)
    × (GL-Cond2 L ↔ GL-Cond3 L))
  ×
  (L ⊆ M⟨ gR , FLRules ⟩
  → (GR-Cond1 L ↔ GR-Cond2 L)
    × (GR-Cond2 L ↔ GR-Cond3 L))

corollary1-from-theorem3
  : (L : Entailment)
  → theorem3 gL L
  → theorem3 gR L
  → corollary1 L
corollary1-from-theorem3 L t19L t19R =
  leftPart
  ,
  rightPart
  where
  ln-gL : LeftNucleus gL FL
  ln-gL = fst remark6

  rn-gR : RightNucleus gR FL
  rn-gR = snd remark6

  leftPart
    : L ⊆ M⟨ gL , FLRules ⟩
    → (GL-Cond1 L ↔ GL-Cond2 L)
      × (GL-Cond2 L ↔ GL-Cond3 L)
  leftPart l⊆m = t19L (inj₂ (inj₁ ln-gL)) l⊆m

  rightPart
    : L ⊆ M⟨ gR , FLRules ⟩
    → (GR-Cond1 L ↔ GR-Cond2 L)
      × (GR-Cond2 L ↔ GR-Cond3 L)
  rightPart l⊆m = t19R (inj₁ rn-gR) l⊆m

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

corollary1-proof : ∀ {R} → FLRules ⊆R R → corollary1 (Deriv R)
corollary1-proof {R} iFL =
  corollary1-from-theorem3 (Deriv R)
    (gL-t3 iFL)
    (gR-t3 iFL)

corollary2 : Type₁
corollary2 =
  (∀ {R} → FLeRules ⊆R R → Deriv R ⊆ InFLe
   → (Ono-Cond1 (Deriv R) ↔ Ono-Cond2 (Deriv R))
     × (Ono-Cond2 (Deriv R) ↔ Ono-Cond3 (Deriv R)))
  ×
  (∀ {R} → MinRules ⊆R R → Deriv R ⊆ Cla
   → (Odintsov-Cond1 (Deriv R) ↔ Odintsov-Cond2 (Deriv R))
     × (Odintsov-Cond2 (Deriv R) ↔ Odintsov-Cond3 (Deriv R)))
  ×
  Glivenko-Cond

-- Ono equivalences (nn over FLeRules)

ono-cond2→cond1
  : ∀ {R}
  → Deriv R ⊆ InFLe
  → Ono-Cond2 (Deriv R)
  → Ono-Cond1 (Deriv R)
ono-cond2→cond1 l⊆m g⊆l {Γ} {a} =
  intro (λ d → g⊆l (m→gj nn-expansive d)) (λ d → destab-M (l⊆m d))

ono-cond1→cond2
  : ∀ {R}
  → FLeRules ⊆R R
  → Ono-Cond1 (Deriv R)
  → Ono-Cond2 (Deriv R)
ono-cond1→cond2 {R} iFLe c1 = g→l
  where
  m⊆k : InFLe ⊆ Kj nn (Deriv R)
  m⊆k {Γ} {a} d = to (c1 {Γ = Γ} {a = a}) d

  g⊆k : G⟨ nn , FLeRules ⟩ ⊆ Kj nn (Deriv R)
  g⊆k d = m⊆k (g⊆m nn-expansive d)

  jj→j : ∀ b → Deriv R (singleton (nn (nn b))) (nn b)
  jj→j b = m⊆k d
    where
    lj+M : Lj+ nn (M⟨ nn , FLeRules ⟩)
    lj+M = jstab→lj+ (λ a → jstab-in-M {j = nn} {R = FLeRules} {a = a})

    d : M⟨ nn , FLeRules ⟩ (singleton (nn (nn b))) b
    d = lj+M {U = []} {V = []} {a = nn b} {b = b} jstab-in-M

  mutual

    g→l-all
      : ∀ {ps}
      → PremisesHold (G⟨ nn , FLeRules ⟩) ps
      → PremisesHold (Deriv R) ps
    g→l-all {ps = []} []ᵃ = []ᵃ
    g→l-all {ps = p ∷ ps} (d ∷ᵃ ds) = g→l d ∷ᵃ g→l-all ds

    g→l
      : G⟨ nn , FLeRules ⟩ ⊆ Deriv R
    g→l Refl = Refl
    g→l (Trans d d₁) = Trans (g→l d) (g→l d₁)
    g→l (ByRule (inl rr) ds) = ByRule (iFLe rr) (g→l-all ds)
    g→l {Γ} (ByRule (inr (inl (lj-instance {b = b}))) ds) =
      transportCtx {L = Deriv R} {b = nn b} (++-unit-r Γ)
        (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = nn (nn b)} {b = nn b}
          (g⊆k (ByRule (inr (inl (lj-instance {b = b}))) ds))
          (jj→j b))
    g→l {Γ} (ByRule (inr (inr (rj-instance {r = r} rr))) ds) =
      transportCtx {L = Deriv R} {b = nn (obj (conclusion r))} (++-unit-r Γ)
        (Trans {U = Γ} {V₁ = []} {V₂ = []}
          {a = nn (nn (obj (conclusion r)))}
          {b = nn (obj (conclusion r))}
          (g⊆k (ByRule (inr (inr (rj-instance rr))) ds))
          (jj→j (obj (conclusion r))))

ono-cond2→cond3
  : ∀ {R}
  → Ono-Cond2 (Deriv R)
  → Ono-Cond3 (Deriv R)
ono-cond2→cond3 g⊆l =
  (λ {a} {b} → g⊆l (shiftCoreInG-FLe (shift∧-instance {a = a} {b = b}) []ᵃ))
  ,
  (λ {a} {b} → g⊆l (shiftCoreInG-FLe (shift⊸-instance {a = a} {b = b}) []ᵃ))

shift›-from-shift⊸
  : ∀ {R}
  → FLeRules ⊆R R
  → Shift⊸ nn (Deriv R)
  → Shift› nn (Deriv R)
shift›-from-shift⊸ {R} iFLe s⊸ {a} {b} =
  transportCtx {L = Deriv R} (++-unit-r (singleton (nn b `› a)))
    (Trans {U = singleton (nn b `› a)} {V₁ = []} {V₂ = []}
      d2 d5)
  where
  iFL : FLRules ⊆R R
  iFL rr = iFLe (inj₁ rr)
  iComm : CommRules ⊆R R
  iComm rr = iFLe (inj₂ rr)
  ljR : Lj nn (Deriv R)
  ljR = BiProgressiveR.biProgressiveR nn-biProgressiveR-FLe iFLe
  -- [nn b › a] ⊢ a ⊸ nn b
  d1 : Deriv R (singleton (nn b `› a)) (a `⊸ nn b)
  d1 = remark4-2-›→⊸ iFL iComm
  -- Trans with s⊸: [nn b › a] ⊢ nn(a ⊸ b)
  d2 : Deriv R (singleton (nn b `› a)) (nn (a `⊸ b))
  d2 = transportCtx {L = Deriv R} (++-unit-r (singleton (nn b `› a)))
    (Trans {U = singleton (nn b `› a)} {V₁ = []} {V₂ = []} d1 s⊸)
  -- [a ⊸ b] ⊢ b › a
  d3 : Deriv R (singleton (a `⊸ b)) (b `› a)
  d3 = remark4-2-⊸→› iFL iComm
  -- Rj: [a ⊸ b] ⊢ nn(b › a)
  d4 : Deriv R (singleton (a `⊸ b)) (nn (b `› a))
  d4 = Rnn-R iFLe d3
  -- Lj at singleton: [nn(a ⊸ b)] ⊢ nn(b › a)
  d5 : Deriv R (singleton (nn (a `⊸ b))) (nn (b `› a))
  d5 = ljR {U = []} {V = []} {a = a `⊸ b} {b = b `› a} d4

ono-cond3→cond2
  : ∀ {R}
  → FLeRules ⊆R R
  → Ono-Cond3 (Deriv R)
  → Ono-Cond2 (Deriv R)
ono-cond3→cond2 {R} iFLe (s∧ , s⊸) d = ext⊆l (g⊆ext d)
  where
  embed : (FLeRules ∪R CommRules) ⊆R FLeRules
  embed (inl r) = r
  embed (inr cr) = inr cr

  s· : Shift· nn (Deriv R)
  s· = lift-⊆R (iFLe ∘ embed) (lemma1-2-proof inj₁ nn-expansive (inl nn-leftProgR))

  s› : Shift› nn (Deriv R)
  s› = shift›-from-shift⊸ iFLe s⊸

  g⊆ext : G⟨ nn , FLeRules ⟩ ⊆ L⟨ ShiftCoreExt nn FLeRules ⟩
  g⊆ext = fst (lemma2-FLe nn-expansive nn-biProgressiveR-FLe)

  mutual

    ext⊆l-all
      : ∀ {ps}
      → PremisesHold (L⟨ ShiftCoreExt nn FLeRules ⟩) ps
      → PremisesHold (Deriv R) ps
    ext⊆l-all {ps = []} []ᵃ = []ᵃ
    ext⊆l-all {ps = p ∷ ps} (d ∷ᵃ ds) = ext⊆l d ∷ᵃ ext⊆l-all ds

    ext⊆l
      : L⟨ ShiftCoreExt nn FLeRules ⟩ ⊆ Deriv R
    ext⊆l Refl = Refl
    ext⊆l (Trans d d₁) = Trans (ext⊆l d) (ext⊆l d₁)
    ext⊆l (ByRule (inl rr) ds) = ByRule (iFLe rr) (ext⊆l-all ds)
    ext⊆l (ByRule (inr (shift·-instance {a = a} {b = b})) []ᵃ) = s· {a} {b}
    ext⊆l (ByRule (inr (shift∧-instance {a = a} {b = b})) []ᵃ) = s∧ {a} {b}
    ext⊆l (ByRule (inr (shift⊸-instance {a = a} {b = b})) []ᵃ) = s⊸ {a} {b}
    ext⊆l (ByRule (inr (shift›-instance {a = a} {b = b})) []ᵃ) = s› {a} {b}

-- Odintsov equivalences (nn over MinRules)

odintsov-cond2→cond1
  : ∀ {R}
  → Deriv R ⊆ Cla
  → Odintsov-Cond2 (Deriv R)
  → Odintsov-Cond1 (Deriv R)
odintsov-cond2→cond1 l⊆m g⊆l {Γ} {a} =
  intro (λ d → g⊆l (m→gj nn-expansive-Min d)) (λ d → destab-M (l⊆m d))

odintsov-cond1→cond2
  : ∀ {R}
  → MinRules ⊆R R
  → Odintsov-Cond1 (Deriv R)
  → Odintsov-Cond2 (Deriv R)
odintsov-cond1→cond2 {R} iMin c1 = g→l
  where
  m⊆k : Cla ⊆ Kj nn (Deriv R)
  m⊆k {Γ} {a} d = to (c1 {Γ = Γ} {a = a}) d

  g⊆k : Gli ⊆ Kj nn (Deriv R)
  g⊆k d = m⊆k (g⊆m nn-expansive-Min d)

  jj→j : ∀ b → Deriv R (singleton (nn (nn b))) (nn b)
  jj→j b = m⊆k d
    where
    lj+M : Lj+ nn (M⟨ nn , MinRules ⟩)
    lj+M = jstab→lj+ (λ a → jstab-in-M {j = nn} {R = MinRules} {a = a})

    d : M⟨ nn , MinRules ⟩ (singleton (nn (nn b))) b
    d = lj+M {U = []} {V = []} {a = nn b} {b = b} jstab-in-M

  mutual

    g→l-all
      : ∀ {ps}
      → PremisesHold Gli ps
      → PremisesHold (Deriv R) ps
    g→l-all {ps = []} []ᵃ = []ᵃ
    g→l-all {ps = p ∷ ps} (d ∷ᵃ ds) = g→l d ∷ᵃ g→l-all ds

    g→l
      : Gli ⊆ Deriv R
    g→l Refl = Refl
    g→l (Trans d d₁) = Trans (g→l d) (g→l d₁)
    g→l (ByRule (inl rr) ds) = ByRule (iMin rr) (g→l-all ds)
    g→l {Γ} (ByRule (inr (inl (lj-instance {b = b}))) ds) =
      transportCtx {L = Deriv R} {b = nn b} (++-unit-r Γ)
        (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = nn (nn b)} {b = nn b}
          (g⊆k (ByRule (inr (inl (lj-instance {b = b}))) ds))
          (jj→j b))
    g→l {Γ} (ByRule (inr (inr (rj-instance {r = r} rr))) ds) =
      transportCtx {L = Deriv R} {b = nn (obj (conclusion r))} (++-unit-r Γ)
        (Trans {U = Γ} {V₁ = []} {V₂ = []}
          {a = nn (nn (obj (conclusion r)))}
          {b = nn (obj (conclusion r))}
          (g⊆k (ByRule (inr (inr (rj-instance rr))) ds))
          (jj→j (obj (conclusion r))))

odintsov-cond2→cond3
  : ∀ {R}
  → Odintsov-Cond2 (Deriv R)
  → Odintsov-Cond3 (Deriv R)
odintsov-cond2→cond3 g⊆l {a} {b} =
  g⊆l (shiftCoreInG-Min (shift⊸-instance {a = a} {b = b}) []ᵃ)

odintsov-cond3→cond2
  : ∀ {R}
  → MinRules ⊆R R
  → Odintsov-Cond3 (Deriv R)
  → Odintsov-Cond2 (Deriv R)
odintsov-cond3→cond2 {R} iMin s⊸ d = ext⊆l (g⊆ext d)
  where
  iFLe : FLeRules ⊆R R
  iFLe rr = iMin (fle⊆min rr)

  embed-comm : (FLeRules ∪R CommRules) ⊆R MinRules
  embed-comm (inl fle) = fle⊆min fle
  embed-comm (inr cr) = inr (inl cr)

  embed-struct : (FLeRules ∪R CommRules ∪R MonoRules ∪R ContrRules) ⊆R MinRules
  embed-struct (inl fle) = fle⊆min fle
  embed-struct (inr struct) = inr struct

  s· : Shift· nn (Deriv R)
  s· = lift-⊆R (iMin ∘ embed-comm)
    (lemma1-2-proof inj₁ nn-expansive (inl nn-leftProgR))

  s∧ : Shift∧ nn (Deriv R)
  s∧ = lift-⊆R (iMin ∘ embed-struct)
    (lemma1-3-proof inj₁ nn-expansive (inl nn-leftProgR))

  s› : Shift› nn (Deriv R)
  s› = shift›-from-shift⊸ iFLe s⊸

  g⊆ext : Gli ⊆ L⟨ ShiftCoreExt nn MinRules ⟩
  g⊆ext = fst (lemma2-Min nn-expansive-Min nn-biProgressiveR-Min)

  mutual

    ext⊆l-all
      : ∀ {ps}
      → PremisesHold (L⟨ ShiftCoreExt nn MinRules ⟩) ps
      → PremisesHold (Deriv R) ps
    ext⊆l-all {ps = []} []ᵃ = []ᵃ
    ext⊆l-all {ps = p ∷ ps} (d ∷ᵃ ds) = ext⊆l d ∷ᵃ ext⊆l-all ds

    ext⊆l
      : L⟨ ShiftCoreExt nn MinRules ⟩ ⊆ Deriv R
    ext⊆l Refl = Refl
    ext⊆l (Trans d d₁) = Trans (ext⊆l d) (ext⊆l d₁)
    ext⊆l (ByRule (inl rr) ds) = ByRule (iMin rr) (ext⊆l-all ds)
    ext⊆l (ByRule (inr (shift·-instance {a = a} {b = b})) []ᵃ) = s· {a} {b}
    ext⊆l (ByRule (inr (shift∧-instance {a = a} {b = b})) []ᵃ) = s∧ {a} {b}
    ext⊆l (ByRule (inr (shift⊸-instance {a = a} {b = b})) []ᵃ) = s⊸ {a} {b}
    ext⊆l (ByRule (inr (shift›-instance {a = a} {b = b})) []ᵃ) = s› {a} {b}

-- Glivenko condition (nn over IntRules)

iFLInt : FLRules ⊆R IntRules
iFLInt rr = inl (inl rr)

iCommInt : CommRules ⊆R IntRules
iCommInt rr = inl (inr (inl rr))

iMonoInt : MonoRules ⊆R IntRules
iMonoInt rr = inl (inr (inr (inl rr)))

iContrInt : ContrRules ⊆R IntRules
iContrInt rr = inl (inr (inr (inr rr)))

mutual

  int⊆cla-all
    : ∀ {ps}
    → PremisesHold Int ps
    → PremisesHold Cla ps
  int⊆cla-all {ps = []} []ᵃ = []ᵃ
  int⊆cla-all {ps = p ∷ ps} (d ∷ᵃ ds) = int⊆cla d ∷ᵃ int⊆cla-all ds

  int⊆cla
    : Int ⊆ Cla
  int⊆cla Refl = Refl
  int⊆cla (Trans d d₁) = Trans (int⊆cla d) (int⊆cla d₁)
  int⊆cla (ByRule (inl rr) ds) = ByRule (inl rr) (int⊆cla-all ds)
  int⊆cla (ByRule (inr (l0-instance {U = U} {V = V} {c = c})) []ᵃ) = l0-in-M {U = U} {V = V} {c = c}

shift⊸-nn-Int : Shift⊸ nn Int
shift⊸-nn-Int {a} {b} =
  ByRule
    (iFLInt (R⊸ {U = singleton h} {a = k} {b = `0}))
    (zero-from-kh ∷ᵃ []ᵃ)
  where
  h : Formula
  h = a `⊸ nn b

  k : Formula
  k = (a `⊸ b) `⊸ `0

  monoInt : Mono Int
  monoInt = mono-from-rules iMonoInt

  contrInt : Contr Int
  contrInt = contr-from-rules iContrInt

  a⊸b-from-b : Int (singleton b) (a `⊸ b)
  a⊸b-from-b =
    ByRule
      (iFLInt (R⊸ {U = singleton b} {a = a} {b = b}))
      (monoInt {U₁ = []} {U₂ = singleton b} {a = a} {b = b} Refl ∷ᵃ []ᵃ)

  notB-from-k : Int (singleton k) (b `⊸ `0)
  notB-from-k =
    ByRule
      (iFLInt (R⊸ {U = singleton k} {a = b} {b = `0}))
      (mid ∷ᵃ []ᵃ)
    where
    mp-k : Int ((a `⊸ b) ∷ k ∷ []) `0
    mp-k = mp⊸-in {R = IntRules} {a = a `⊸ b} {b = `0} iFLInt

    mid : Int (b ∷ k ∷ []) `0
    mid = Trans {U = singleton b} {V₁ = []} {V₂ = singleton k} a⊸b-from-b mp-k

  nnB-from-ah : Int (a ∷ singleton h) (nn b)
  nnB-from-ah = mp⊸-in {R = IntRules} {a = a} {b = nn b} iFLInt

  notA-from-kh : Int (k ∷ h ∷ []) (a `⊸ `0)
  notA-from-kh =
    ByRule
      (iFLInt (R⊸ {U = k ∷ h ∷ []} {a = a} {b = `0}))
      (swapped ∷ᵃ []ᵃ)
    where
    mp-nn : Int ((b `⊸ `0) ∷ nn b ∷ []) `0
    mp-nn = mp⊸-in {R = IntRules} {a = b `⊸ `0} {b = `0} iFLInt

    use-nn : Int ((b `⊸ `0) ∷ a ∷ h ∷ []) `0
    use-nn =
      Trans {U = a ∷ h ∷ []} {V₁ = singleton (b `⊸ `0)} {V₂ = []}
        nnB-from-ah
        mp-nn

    mid : Int (k ∷ a ∷ h ∷ []) `0
    mid =
      Trans {U = singleton k} {V₁ = []} {V₂ = a ∷ h ∷ []}
        notB-from-k
        use-nn

    swapped : Int (a ∷ k ∷ h ∷ []) `0
    swapped = comm-from-rules iCommInt {U₁ = []} {U₂ = singleton h} {a₁ = k} {a₂ = a} {b = `0} mid

  ab-from-kh : Int (k ∷ h ∷ []) (a `⊸ b)
  ab-from-kh =
    ByRule
      (iFLInt (R⊸ {U = k ∷ h ∷ []} {a = a} {b = b}))
      (mid ∷ᵃ []ᵃ)
    where
    mp-notA : Int (a ∷ (a `⊸ `0) ∷ []) `0
    mp-notA = mp⊸-in {R = IntRules} {a = a} {b = `0} iFLInt

    explode : Int (singleton `0) b
    explode = ByRule (inr (l0-instance {U = []} {V = []} {c = b})) []ᵃ

    to-zero : Int (a ∷ k ∷ h ∷ []) `0
    to-zero =
      Trans {U = k ∷ h ∷ []} {V₁ = singleton a} {V₂ = []}
        notA-from-kh
        mp-notA

    mid : Int (a ∷ k ∷ h ∷ []) b
    mid = Trans {U = a ∷ k ∷ h ∷ []} {V₁ = []} {V₂ = []} to-zero explode

  zero-from-kh : Int (k ∷ h ∷ []) `0
  zero-from-kh = contrInt {U₁ = []} {U₂ = singleton h} {a = k} {b = `0} duplicated
    where
    mp-k-swapped : Int (k ∷ (a `⊸ b) ∷ []) `0
    mp-k-swapped =
      comm-from-rules iCommInt {U₁ = []} {U₂ = []} {a₁ = a `⊸ b} {a₂ = k} {b = `0}
        (mp⊸-in {R = IntRules} {a = a `⊸ b} {b = `0} iFLInt)

    duplicated : Int (k ∷ k ∷ h ∷ []) `0
    duplicated =
      Trans {U = k ∷ h ∷ []} {V₁ = singleton k} {V₂ = []}
        ab-from-kh
        mp-k-swapped

gli⊆int : Gli ⊆ Int
gli⊆int = odintsov-cond3→cond2 MinRules⊆IntRules shift⊸-nn-Int

glivenko-cond-proof : Glivenko-Cond
glivenko-cond-proof = odintsov-cond2→cond1 int⊆cla gli⊆int

corollary2-proof : corollary2
corollary2-proof =
  (λ iFLe l⊆m →
    intro (ono-cond1→cond2 iFLe) (ono-cond2→cond1 l⊆m)
    ,
    intro ono-cond2→cond3 (ono-cond3→cond2 iFLe))
  ,
  (λ iMin l⊆m →
    intro (odintsov-cond1→cond2 iMin) (odintsov-cond2→cond1 l⊆m)
    ,
    intro odintsov-cond2→cond3 (odintsov-cond3→cond2 iMin))
  ,
  glivenko-cond-proof
