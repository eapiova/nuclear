module Substructural.FL.Rules where

open import Substructural.Prelude
open import Substructural.FL.Formula
open import Substructural.Core.Judgement Formula
open import Substructural.Core.Rules Formula
open import Substructural.Core.Derivation Formula
open import Substructural.Core.Extensions Formula

private
  variable
    U V W : Ctx
    a b c : Formula

data FLRules : RuleSet where
  L∨
    : ∀ {U V a b c}
    → FLRules
        (mkRule
          ((U ++ a ∷ V ▷ c) ∷ (U ++ b ∷ V ▷ c) ∷ [])
          (U ++ (a ∨ b) ∷ V ▷ c))
  R∨₁
    : ∀ {U a b}
    → FLRules
        (mkRule
          ((U ▷ a) ∷ [])
          (U ▷ a ∨ b))
  R∨₂
    : ∀ {U a b}
    → FLRules
        (mkRule
          ((U ▷ b) ∷ [])
          (U ▷ a ∨ b))
  L∧₁
    : ∀ {U V a b c}
    → FLRules
        (mkRule
          ((U ++ a ∷ V ▷ c) ∷ [])
          (U ++ (a ∧ b) ∷ V ▷ c))
  L∧₂
    : ∀ {U V a b c}
    → FLRules
        (mkRule
          ((U ++ b ∷ V ▷ c) ∷ [])
          (U ++ (a ∧ b) ∷ V ▷ c))
  R∧
    : ∀ {U a b}
    → FLRules
        (mkRule
          ((U ▷ a) ∷ (U ▷ b) ∷ [])
          (U ▷ a ∧ b))
  L1
    : ∀ {U V c}
    → FLRules
        (mkRule
          ((U ++ V ▷ c) ∷ [])
          (U ++ `1 ∷ V ▷ c))
  R1
    : FLRules (mkRule [] ([] ▷ `1))
  L·
    : ∀ {U V a b c}
    → FLRules
        (mkRule
          ((U ++ a ∷ b ∷ V ▷ c) ∷ [])
          (U ++ (a · b) ∷ V ▷ c))
  R·
    : ∀ {U V a b}
    → FLRules
        (mkRule
          ((U ▷ a) ∷ (V ▷ b) ∷ [])
          (U ++ V ▷ a · b))
  L⊸
    : ∀ {U V W a b c}
    → FLRules
        (mkRule
          ((U ▷ a) ∷ (W ++ b ∷ V ▷ c) ∷ [])
          ((W ++ U) ++ (a ⊸ b) ∷ V ▷ c))
  R⊸
    : ∀ {U a b}
    → FLRules
        (mkRule
          ((a ∷ U ▷ b) ∷ [])
          (U ▷ a ⊸ b))
  L›
    : ∀ {U V W a b c}
    → FLRules
        (mkRule
          ((U ▷ a) ∷ (W ++ b ∷ V ▷ c) ∷ [])
          (W ++ (b › a) ∷ (U ++ V) ▷ c))
  R›
    : ∀ {U a b}
    → FLRules
        (mkRule
          ((U ++ a ∷ [] ▷ b) ∷ [])
          (U ▷ b › a))

FL : Entailment
FL = L⟨ FLRules ⟩

StructRules : RuleSet
StructRules = CommRules ∪R MonoRules ∪R ContrRules

FLeRules : RuleSet
FLeRules = FLRules ∪R CommRules

MinRules : RuleSet
MinRules = FLRules ∪R StructRules

data L0Rules : RuleSet where
  l0-instance
    : ∀ {U V c}
    → L0Rules
        (mkRule
          []
          (U ++ `0 ∷ V ▷ c))

IntRules : RuleSet
IntRules = MinRules ∪R L0Rules

FLe : Entailment
FLe = L⟨ FLeRules ⟩

Min : Entailment
Min = L⟨ MinRules ⟩

Int : Entailment
Int = L⟨ IntRules ⟩

FLRules⊆FLeRules : FLRules ⊆R FLeRules
FLRules⊆FLeRules rr = inj₁ rr

FLRules⊆MinRules : FLRules ⊆R MinRules
FLRules⊆MinRules rr = inj₁ rr

MinRules⊆IntRules : MinRules ⊆R IntRules
MinRules⊆IntRules rr = inj₁ rr

FL⊆FLe : FL ⊆ FLe
FL⊆FLe = lift-⊆R FLRules⊆FLeRules

FL⊆Min : FL ⊆ Min
FL⊆Min = lift-⊆R FLRules⊆MinRules

Min⊆Int : Min ⊆ Int
Min⊆Int = lift-⊆R MinRules⊆IntRules
