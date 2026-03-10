module Substructural.FL.DoubleNegation where

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
open import Substructural.Core.Conservation Formula
  using (Mono; transportCtx; comm-from-rules; mono-from-rules; mono-in-M)
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)

nn : Formula → Formula
nn a = (a `⊸ `0) `⊸ `0

-- Helper: 0›a ⊢ a⊸0 (needs Comm to swap mp›)
tilde-to-neg : ∀ {R' a} → FLeRules ⊆R R' → Deriv R' (singleton (`0 `› a)) (a `⊸ `0)
tilde-to-neg {R'} {a} iFLe =
  ByRule (iFL (R⊸ {U = singleton (`0 `› a)} {a = a} {b = `0})) (swapped ∷ᵃ []ᵃ)
  where
  iFL : FLRules ⊆R R'
  iFL rr = iFLe (inj₁ rr)
  -- mp› : (0›a) ∷ a ∷ [] ⊢ 0
  base : Deriv R' ((`0 `› a) ∷ a ∷ []) `0
  base = mp›-in iFL
  -- Comm → a ∷ (0›a) ∷ [] ⊢ 0
  swapped : Deriv R' (a ∷ (`0 `› a) ∷ []) `0
  swapped = comm-from-rules (λ rr → iFLe (inj₂ rr))
    {U₁ = []} {U₂ = []} {a₁ = `0 `› a} {a₂ = a} {b = `0} base

-- Rj nn: Γ ⊢ a → Γ ⊢ nn a (needs Comm)
Rnn-R : ∀ {R'} → FLeRules ⊆R R' → Rj nn (Deriv R')
Rnn-R {R'} iFLe {Γ} {a} d =
  ByRule (iFL (R⊸ {U = Γ} {a = a `⊸ `0} {b = `0})) (d3 ∷ᵃ []ᵃ)
  where
  iFL : FLRules ⊆R R'
  iFL rr = iFLe (inj₁ rr)
  -- mp⊸: a ∷ [a⊸0] ⊢ 0
  d1 : Deriv R' (a ∷ (a `⊸ `0) ∷ []) `0
  d1 = mp⊸-in iFL
  -- Comm → (a⊸0) ∷ [a] ⊢ 0
  d2 : Deriv R' ((a `⊸ `0) ∷ a ∷ []) `0
  d2 = comm-from-rules (λ rr → iFLe (inj₂ rr))
    {U₁ = []} {U₂ = []} {a₁ = a} {a₂ = a `⊸ `0} {b = `0} d1
  -- Trans → (a⊸0) ∷ Γ ⊢ 0
  d3 : Deriv R' ((a `⊸ `0) ∷ Γ) `0
  d3 = transportCtx {L = Deriv R'} (cong ((a `⊸ `0) ∷_) (++-unit-r Γ))
    (Trans {U = Γ} {V₁ = singleton (a `⊸ `0)} {V₂ = []} d d2)

-- Ljleft nn: U++[a] ⊢ nn b → U++[nn a] ⊢ nn b (needs Comm)
Lnn-left-R : ∀ {R'} → FLeRules ⊆R R' → Ljleft nn (Deriv R')
Lnn-left-R {R'} iFLe {U} {a} {b} d =
  ByRule (iFL (R⊸ {U = suffix U (nn a)} {a = b `⊸ `0} {b = `0})) (d5 ∷ᵃ []ᵃ)
  where
  iFL : FLRules ⊆R R'
  iFL rr = iFLe (inj₁ rr)
  -- (b⊸0) ∷ [nn b] ⊢ 0 via mp⊸
  mp-nnb : Deriv R' ((b `⊸ `0) ∷ nn b ∷ []) `0
  mp-nnb = mp⊸-in iFL
  -- Trans → (b⊸0) ∷ U++[a] ⊢ 0
  d2 : Deriv R' ((b `⊸ `0) ∷ (U ++ (a ∷ []))) `0
  d2 = transportCtx {L = Deriv R'} (cong ((b `⊸ `0) ∷_) (++-unit-r (U ++ (a ∷ []))))
    (Trans {U = U ++ (a ∷ [])} {V₁ = singleton (b `⊸ `0)} {V₂ = []} d mp-nnb)
  -- R› → (b⊸0) ∷ U ⊢ 0›a
  d3 : Deriv R' ((b `⊸ `0) ∷ U) (`0 `› a)
  d3 = ByRule (iFL (R› {U = (b `⊸ `0) ∷ U} {a = a} {b = `0})) (d2 ∷ᵃ []ᵃ)
  -- Trans with tilde-to-neg → (b⊸0) ∷ U ⊢ a⊸0
  d4 : Deriv R' ((b `⊸ `0) ∷ U) (a `⊸ `0)
  d4 = transportCtx {L = Deriv R'} (++-unit-r ((b `⊸ `0) ∷ U))
    (Trans {U = (b `⊸ `0) ∷ U} {V₁ = []} {V₂ = []} d3 (tilde-to-neg iFLe))
  -- L⊸ on nn a → (b⊸0) ∷ U++[nn a] ⊢ 0
  d5 : Deriv R' ((b `⊸ `0) ∷ suffix U (nn a)) `0
  d5 =
    ByRule
      (iFL (L⊸ {U = (b `⊸ `0) ∷ U} {V = []} {W = []} {a = a `⊸ `0} {b = `0} {c = `0}))
      (d4 ∷ᵃ Refl ∷ᵃ []ᵃ)

nn-expansive : Expansive nn FLeRules
nn-expansive = mkExpansive (Rnn-R (λ r → r))

nn-leftProgR : LeftProgressiveR nn FLeRules
nn-leftProgR = mkLeftProgressiveR Lnn-left-R

-- Full Lj via ljleft + shift·
nn-biProgressiveR-FLe : BiProgressiveR nn FLeRules
nn-biProgressiveR-FLe = mkBiProgressiveR λ {R'} iR' →
  ljleft+shift·→lj (iFL iR') (Rnn-R iR') (Lnn-left-R iR') (shift·-nn iR')
  where
  iFL : ∀ {R'} → FLeRules ⊆R R' → FLRules ⊆R R'
  iFL iR' rr = iR' (inj₁ rr)
  embed : (FLeRules ∪R CommRules) ⊆R FLeRules
  embed (inl r) = r
  embed (inr cr) = inr cr
  shift·-nn : ∀ {R'} → FLeRules ⊆R R' → Shift· nn (Deriv R')
  shift·-nn iR' =
    lift-⊆R (iR' ∘ embed) (lemma1-2-proof inj₁ nn-expansive (inl nn-leftProgR))

-- Lifting to MinRules
fle⊆min : FLeRules ⊆R MinRules
fle⊆min (inl flr) = inl flr
fle⊆min (inr cr) = inr (inl cr)

nn-expansive-Min : Expansive nn MinRules
nn-expansive-Min = mkExpansive (Rnn-R fle⊆min)

nn-biProgressiveR-Min : BiProgressiveR nn MinRules
nn-biProgressiveR-Min = mkBiProgressiveR λ iMin →
  BiProgressiveR.biProgressiveR nn-biProgressiveR-FLe (λ r → iMin (fle⊆min r))

iMonoMin : MonoRules ⊆R MinRules
iMonoMin mr = inr (inr (inl mr))

zero-derives-nn-Min : ∀ {c} → Min (singleton `0) (nn c)
zero-derives-nn-Min {c} =
  ByRule
    (inl (R⊸ {U = singleton `0} {a = c `⊸ `0} {b = `0}))
    (mid ∷ᵃ []ᵃ)
  where
  monoMin : Mono Min
  monoMin = mono-from-rules iMonoMin

  mid : Min ((c `⊸ `0) ∷ singleton `0) `0
  mid = monoMin {U₁ = []} {U₂ = singleton `0} {a = c `⊸ `0} {b = `0} Refl

zero-derives-all : ∀ {c} → M⟨ nn , MinRules ⟩ (singleton `0) c
zero-derives-all {c} =
  destab-M (lift-base-into-M zero-derives-nn-Min)

prepend-list-M
  : ∀ W {Γ c}
  → M⟨ nn , MinRules ⟩ Γ c
  → M⟨ nn , MinRules ⟩ (W ++ Γ) c
prepend-list-M [] d = d
prepend-list-M (w ∷ W) {Γ} {c} d =
  monoM {U₁ = []} {U₂ = W ++ Γ} {a = w} {b = c}
    (prepend-list-M W d)
  where
  monoM : Mono (M⟨ nn , MinRules ⟩)
  monoM = mono-in-M iMonoMin

append-list-M
  : ∀ W {Γ c}
  → M⟨ nn , MinRules ⟩ Γ c
  → M⟨ nn , MinRules ⟩ (Γ ++ W) c
append-list-M [] {Γ} d =
  transportCtx {L = M⟨ nn , MinRules ⟩} (sym (++-unit-r Γ)) d
append-list-M (w ∷ W) {Γ} {c} d =
  transportCtx {L = M⟨ nn , MinRules ⟩} (++-assoc Γ (w ∷ []) W)
    (append-list-M W step)
  where
  monoM : Mono (M⟨ nn , MinRules ⟩)
  monoM = mono-in-M iMonoMin

  step : M⟨ nn , MinRules ⟩ (Γ ++ (w ∷ [])) c
  step =
    monoM {U₁ = Γ} {U₂ = []} {a = w} {b = c}
      (transportCtx {L = M⟨ nn , MinRules ⟩} (sym (++-unit-r Γ)) d)

l0-in-M : ∀ {U V c} → M⟨ nn , MinRules ⟩ (plug₁ U `0 V) c
l0-in-M {U} {V} {c} =
  prepend-list-M U (append-list-M V zero-derives-all)
