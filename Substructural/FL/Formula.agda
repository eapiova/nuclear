module Substructural.FL.Formula where

open import Substructural.Prelude

infixr 20 _⊸_ _›_ _∘−_
infixr 30 _·_
infixr 40 _∧_
infixr 50 _∨_

data Formula : Type where
  `0 : Formula
  `1 : Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  _·_ : Formula → Formula → Formula
  _⊸_ : Formula → Formula → Formula
  _›_ : Formula → Formula → Formula

_∘−_ : Formula → Formula → Formula
_∘−_ = _›_

∼_ : Formula → Formula
∼ a = a ⊸ `0

−_ : Formula → Formula
− a = `0 › a
