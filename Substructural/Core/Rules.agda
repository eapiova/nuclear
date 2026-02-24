{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Rules {ℓ} (S : Set ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S

-- Glivenko_substructural.pdf, Section 2:
-- non-structural rules are finite premise lists with one conclusion.
record Rule : Type ℓ where
  constructor mkRule
  field
    premises : List Seq
    conclusion : Seq

open Rule public

RuleSet : Type (ℓ-suc ℓ)
RuleSet = Rule → Type ℓ

infix 4 _⊆R_

_⊆R_ : RuleSet → RuleSet → Type ℓ
R ⊆R R' = ∀ {r} → R r → R' r

infixr 5 _∪R_

_∪R_ : RuleSet → RuleSet → RuleSet
(R ∪R R') r = R r ⊎ R' r

mapSuccRule : (S → S) → Rule → Rule
mapSuccRule j r = mkRule (map (mapSucc j) (premises r)) (mapSucc j (conclusion r))

mapBothRule : (S → S) → Rule → Rule
mapBothRule f r = mkRule (map (mapBoth f) (premises r)) (mapBoth f (conclusion r))
