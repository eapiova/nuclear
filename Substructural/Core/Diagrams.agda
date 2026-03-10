open import Cubical.Core.Primitives

module Substructural.Core.Diagrams {ℓ} (S : Type ℓ) where

-- CSL-only diagram API. This module is kept for the 2026 layer and is not part
-- of the paper-facing public surface re-exported by Everything.agda.

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S
open import Substructural.Core.Derivation S
open import Substructural.Core.Nucleus S
open import Substructural.Core.Extensions S
open import Substructural.Core.Conservation S

infix 4 _≃_

_≃_ : Entailment → Entailment → Type ℓ
L ≃ L' = (L ⊆ L') × (L' ⊆ L)

⊆-refl : ∀ {L} → L ⊆ L
⊆-refl d = d

⊆-trans : ∀ {L L' L''} → L ⊆ L' → L' ⊆ L'' → L ⊆ L''
⊆-trans i k d = k (i d)

kj-pres-⊆
  : ∀ {j L L'}
  → L ⊆ L'
  → Kj j L ⊆ Kj j L'
kj-pres-⊆ {j} i {Γ} {a} d = i {Γ = Γ} {a = j a} d

kj-pres-≃
  : ∀ {j L L'}
  → L ≃ L'
  → Kj j L ≃ Kj j L'
kj-pres-≃ {j} (i , k) =
  (λ {Γ} {a} d → i {Γ = Γ} {a = j a} d)
  ,
  (λ {Γ} {a} d → k {Γ = Γ} {a = j a} d)

km⊆m
  : ∀ {j R}
  → Kj j (M⟨ j , R ⟩) ⊆ M⟨ j , R ⟩
km⊆m = destab-M

m⊆km
  : ∀ {j R}
  → Expansive j R
  → M⟨ j , R ⟩ ⊆ Kj j (M⟨ j , R ⟩)
m⊆km {j} {R} e = lift-Expansive e (λ rr → inl rr)

mutual

  m'⊆m-all
    : ∀ {j R R' ps}
    → (∀ {r} → R' r → RuleHoldsIn r (M⟨ j , R ⟩))
    → PremisesHold (M⟨ j , R ∪R R' ⟩) ps
    → PremisesHold (M⟨ j , R ⟩) ps
  m'⊆m-all {ps = []} adm []ᵃ = []ᵃ
  m'⊆m-all {ps = p ∷ ps} adm (d ∷ᵃ ds) = m'⊆m adm d ∷ᵃ m'⊆m-all adm ds

  m'⊆m
    : ∀ {j R R'}
    → (∀ {r} → R' r → RuleHoldsIn r (M⟨ j , R ⟩))
    → M⟨ j , R ∪R R' ⟩ ⊆ M⟨ j , R ⟩
  m'⊆m adm Refl = Refl
  m'⊆m adm (Trans d d₁) = Trans (m'⊆m adm d) (m'⊆m adm d₁)
  m'⊆m adm (ByRule (inl (inl rr)) ds) = ByRule (inl rr) (m'⊆m-all adm ds)
  m'⊆m adm (ByRule (inl (inr rr')) ds) = adm rr' (m'⊆m-all adm ds)
  m'⊆m adm (ByRule (inr jstab-instance) ds) = ByRule (inr jstab-instance) []ᵃ

kjG⊆kjM
  : ∀ {j R}
  → Expansive j R
  → Kj j (G⟨ j , R ⟩) ⊆ Kj j (M⟨ j , R ⟩)
kjG⊆kjM e d = g⊆m e d

kjM⊆kjG
  : ∀ {j R}
  → Expansive j R
  → Kj j (M⟨ j , R ⟩) ⊆ Kj j (G⟨ j , R ⟩)
kjM⊆kjG e d = m→gj e (destab-M d)

base⊆extension
  : ∀ {R R'}
  → L⟨ R ⟩ ⊆ L⟨ R ∪R R' ⟩
base⊆extension = lift-⊆R inj₁

theorem1-1
  : ∀ {j R R'}
  → Expansive j R
  → L⟨ R ∪R R' ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩)
theorem1-1 e = fst (theorem1 e)

theorem1-2
  : ∀ {j R R'}
  → Expansive j R
  → (Kj j (L⟨ R ∪R R' ⟩) ⊆ L⟨ R ∪R R' ⟩) ↔ (M⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩)
theorem1-2 e = fst (snd (theorem1 e))

theorem1-3
  : ∀ {j R R'}
  → Expansive j R
  → (Kj j (L⟨ R ∪R R' ⟩) ⊆ M⟨ j , R ⟩) ↔ (L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩)
theorem1-3 e = fst (snd (snd (theorem1 e)))

theorem1-4
  : ∀ {j R R'}
  → Expansive j R
  → (M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩)) ↔ (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩)
theorem1-4 e = snd (snd (snd (theorem1 e)))

record BaseDiagram (j : S → S) (R : RuleSet) : Type ℓ where
  field
    L⊆G : L⟨ R ⟩ ⊆ G⟨ j , R ⟩
    G⊆M : G⟨ j , R ⟩ ⊆ M⟨ j , R ⟩

    L⊆KL : L⟨ R ⟩ ⊆ Kj j (L⟨ R ⟩)
    G⊆KG : G⟨ j , R ⟩ ⊆ Kj j (G⟨ j , R ⟩)
    M⊆KM : M⟨ j , R ⟩ ⊆ Kj j (M⟨ j , R ⟩)

    KL⊆KG : Kj j (L⟨ R ⟩) ⊆ Kj j (G⟨ j , R ⟩)
    KG⊆KM : Kj j (G⟨ j , R ⟩) ⊆ Kj j (M⟨ j , R ⟩)
    KM⊆KG : Kj j (M⟨ j , R ⟩) ⊆ Kj j (G⟨ j , R ⟩)

    KL⊆M : Kj j (L⟨ R ⟩) ⊆ M⟨ j , R ⟩

baseDiagram
  : ∀ {j R}
  → Expansive j R
  → BaseDiagram j R
baseDiagram {j} {R} e with proposition1 {j} {R} e
... | l⊆k , l⊆g , g⊆m' , kl⊆m' =
  record
    { L⊆G = l⊆g
    ; G⊆M = g⊆m'

    ; L⊆KL = l⊆k
    ; G⊆KG = lift-Expansive e (λ rr → inl rr)
    ; M⊆KM = m⊆km e

    ; KL⊆KG = λ d → l⊆g d
    ; KG⊆KM = kjG⊆kjM e
    ; KM⊆KG = kjM⊆kjG e

    ; KL⊆M = kl⊆m'
    }

record Page8Diagram (j : S → S) (R R₁ R₂ R₃ : RuleSet) : Type ℓ where
  field
    L⊆L₁ : L⟨ R ⟩ ⊆ L⟨ R ∪R R₁ ⟩
    L₁⊆G : L⟨ R ∪R R₁ ⟩ ⊆ G⟨ j , R ⟩
    G⊆L₂ : G⟨ j , R ⟩ ⊆ L⟨ R ∪R R₂ ⟩
    L₂⊆M : L⟨ R ∪R R₂ ⟩ ⊆ M⟨ j , R ⟩
    M⊆L₃ : M⟨ j , R ⟩ ⊆ L⟨ R ∪R R₃ ⟩

    L⊆KL : L⟨ R ⟩ ⊆ Kj j (L⟨ R ⟩)
    L₁⊆KL₁ : L⟨ R ∪R R₁ ⟩ ⊆ Kj j (L⟨ R ∪R R₁ ⟩)
    G⊆KG : G⟨ j , R ⟩ ⊆ Kj j (G⟨ j , R ⟩)
    L₂⊆KL₂ : L⟨ R ∪R R₂ ⟩ ⊆ Kj j (L⟨ R ∪R R₂ ⟩)
    M⊆KM : M⟨ j , R ⟩ ⊆ Kj j (M⟨ j , R ⟩)
    L₃⊆KL₃ : L⟨ R ∪R R₃ ⟩ ⊆ Kj j (L⟨ R ∪R R₃ ⟩)

    KL⊆KL₁ : Kj j (L⟨ R ⟩) ⊆ Kj j (L⟨ R ∪R R₁ ⟩)
    KL₁⊆KG : Kj j (L⟨ R ∪R R₁ ⟩) ⊆ Kj j (G⟨ j , R ⟩)
    KG⊆KL₂ : Kj j (G⟨ j , R ⟩) ⊆ Kj j (L⟨ R ∪R R₂ ⟩)
    KL₂⊆KM : Kj j (L⟨ R ∪R R₂ ⟩) ⊆ Kj j (M⟨ j , R ⟩)
    KM⊆KL₃ : Kj j (M⟨ j , R ⟩) ⊆ Kj j (L⟨ R ∪R R₃ ⟩)

    KG⊆KM : Kj j (G⟨ j , R ⟩) ⊆ Kj j (M⟨ j , R ⟩)
    KM⊆KG : Kj j (M⟨ j , R ⟩) ⊆ Kj j (G⟨ j , R ⟩)

    KL₂⊆KG : Kj j (L⟨ R ∪R R₂ ⟩) ⊆ Kj j (G⟨ j , R ⟩)
    KM⊆KL₂ : Kj j (M⟨ j , R ⟩) ⊆ Kj j (L⟨ R ∪R R₂ ⟩)

    KM⊆M : Kj j (M⟨ j , R ⟩) ⊆ M⟨ j , R ⟩
    KL₃⊆L₃ : Kj j (L⟨ R ∪R R₃ ⟩) ⊆ L⟨ R ∪R R₃ ⟩

page8Diagram
  : ∀ {j R R₁ R₂ R₃}
  → Expansive j R
  → (L⟨ R ∪R R₁ ⟩ ⊆ G⟨ j , R ⟩)
  → (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R₂ ⟩)
  → (L⟨ R ∪R R₂ ⟩ ⊆ M⟨ j , R ⟩)
  → (M⟨ j , R ⟩ ⊆ L⟨ R ∪R R₃ ⟩)
  → Page8Diagram j R R₁ R₂ R₃
page8Diagram {j} {R} {R₁} {R₂} {R₃} e l₁⊆g g⊆l₂ l₂⊆m m⊆l₃ =
  record
    { L⊆L₁ = base⊆extension {R = R} {R' = R₁}
    ; L₁⊆G = l₁⊆g
    ; G⊆L₂ = g⊆l₂
    ; L₂⊆M = l₂⊆m
    ; M⊆L₃ = m⊆l₃

    ; L⊆KL = onBase-Expansive e
    ; L₁⊆KL₁ = theorem1-1 {R' = R₁} e
    ; G⊆KG = lift-Expansive e (λ rr → inl rr)
    ; L₂⊆KL₂ = theorem1-1 {R' = R₂} e
    ; M⊆KM = m⊆km e
    ; L₃⊆KL₃ = theorem1-1 {R' = R₃} e

    ; KL⊆KL₁ = λ d → base⊆extension {R = R} {R' = R₁} d
    ; KL₁⊆KG = kl₁⊆kg
    ; KG⊆KL₂ = λ d → g⊆l₂ d
    ; KL₂⊆KM = λ d → l₂⊆m d
    ; KM⊆KL₃ = λ d → m⊆l₃ d

    ; KG⊆KM = kjG⊆kjM e
    ; KM⊆KG = kjM⊆kjG e

    ; KL₂⊆KG = λ d → kjM⊆kjG e (l₂⊆m d)
    ; KM⊆KL₂ = λ d → g⊆l₂ (kjM⊆kjG e d)

    ; KM⊆M = km⊆m
    ; KL₃⊆L₃ = from (theorem1-2 {R' = R₃} e) m⊆l₃
    }
  where
  l₁⊆m : L⟨ R ∪R R₁ ⟩ ⊆ M⟨ j , R ⟩
  l₁⊆m d = g⊆m e (l₁⊆g d)

  kl₁⊆m : Kj j (L⟨ R ∪R R₁ ⟩) ⊆ M⟨ j , R ⟩
  kl₁⊆m d = from (theorem1-3 {R' = R₁} e) l₁⊆m d

  kl₁⊆kg : Kj j (L⟨ R ∪R R₁ ⟩) ⊆ Kj j (G⟨ j , R ⟩)
  kl₁⊆kg d = kjM⊆kjG e (m⊆km e (kl₁⊆m d))

  kj-pres-⊆m
    : L⟨ R ∪R R₂ ⟩ ⊆ M⟨ j , R ⟩
    → Kj j (L⟨ R ∪R R₂ ⟩) ⊆ Kj j (M⟨ j , R ⟩)
  kj-pres-⊆m i d = i d

record Case1 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    l⊆l' : L⟨ R ⟩ ⊆ L⟨ R ∪R R' ⟩
    g⊆g' : G⟨ j , R ⟩ ⊆ G⟨ j , R ∪R R' ⟩
    m⊆m' : M⟨ j , R ⟩ ⊆ M⟨ j , R ∪R R' ⟩

    kl⊆kl' : Kj j (L⟨ R ⟩) ⊆ Kj j (L⟨ R ∪R R' ⟩)
    kg⊆kg' : Kj j (G⟨ j , R ⟩) ⊆ Kj j (G⟨ j , R ∪R R' ⟩)
    km⊆km' : Kj j (M⟨ j , R ⟩) ⊆ Kj j (M⟨ j , R ∪R R' ⟩)

    base : BaseDiagram j R
    base' : BaseDiagram j (R ∪R R')

case1
  : ∀ {j R R'}
  → Expansive j R
  → Case1 j R R'
case1 {j} {R} {R'} e =
  record
    { l⊆l' = base⊆extension {R = R} {R' = R'}
    ; g⊆g' = lift-G (λ rr → inl rr)
    ; m⊆m' = lift-M (λ rr → inl rr)

    ; kl⊆kl' = λ d → base⊆extension {R = R} {R' = R'} d
    ; kg⊆kg' = λ d → lift-G (λ rr → inl rr) d
    ; km⊆km' = λ d → lift-M (λ rr → inl rr) d

    ; base = baseDiagram e
    ; base' = baseDiagram e'
    }
  where
  e' : Expansive j (R ∪R R')
  e' = mkExpansive (lift-Expansive e inj₁)

record Case2 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'
    l'⊆m : L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩
    kl'⊆m : Kj j (L⟨ R ∪R R' ⟩) ⊆ M⟨ j , R ⟩
    m'⊆m-arrow : M⟨ j , R ∪R R' ⟩ ⊆ M⟨ j , R ⟩
    km'⊆km : Kj j (M⟨ j , R ∪R R' ⟩) ⊆ Kj j (M⟨ j , R ⟩)

case2
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩)
  → (∀ {r} → R' r → RuleHoldsIn r (M⟨ j , R ⟩))
  → Case2 j R R'
case2 {j} {R} {R'} e l'⊆m adm =
  record
    { common = case1 e
    ; l'⊆m = l'⊆m
    ; kl'⊆m = from (theorem1-3 {R' = R'} e) l'⊆m
    ; m'⊆m-arrow = m'⊆m adm
    ; km'⊆km = λ d → m'⊆m adm d
    }

record Case3 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'
    l'⊆g : L⟨ R ∪R R' ⟩ ⊆ G⟨ j , R ⟩

    g≃g' : G⟨ j , R ⟩ ≃ G⟨ j , R ∪R R' ⟩
    m≃m' : M⟨ j , R ⟩ ≃ M⟨ j , R ∪R R' ⟩

    kg≃kg' : Kj j (G⟨ j , R ⟩) ≃ Kj j (G⟨ j , R ∪R R' ⟩)
    km≃km' : Kj j (M⟨ j , R ⟩) ≃ Kj j (M⟨ j , R ∪R R' ⟩)

case3
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ⊆ G⟨ j , R ⟩)
  → (G⟨ j , R ∪R R' ⟩ ⊆ G⟨ j , R ⟩)
  → (∀ {r} → R' r → RuleHoldsIn r (M⟨ j , R ⟩))
  → Case3 j R R'
case3 {j} {R} {R'} e l'⊆g g'⊆g adm =
  record
    { common = case1 e
    ; l'⊆g = l'⊆g

    ; g≃g' = lift-G (λ rr → inl rr) , g'⊆g
    ; m≃m' = lift-M (λ rr → inl rr) , m'⊆m adm

    ; kg≃kg' =
        (λ d → lift-G (λ rr → inl rr) d)
        ,
        (λ d → g'⊆g d)
    ; km≃km' =
        (λ d → lift-M (λ rr → inl rr) d)
        ,
        (λ d → m'⊆m adm d)
    }

record Case4 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'

    l'≃g' : L⟨ R ∪R R' ⟩ ≃ G⟨ j , R ∪R R' ⟩
    m≃m' : M⟨ j , R ⟩ ≃ M⟨ j , R ∪R R' ⟩

    m≃kl' : M⟨ j , R ⟩ ≃ Kj j (L⟨ R ∪R R' ⟩)
    kg≃kl' : Kj j (G⟨ j , R ⟩) ≃ Kj j (L⟨ R ∪R R' ⟩)
    kl'≃kg' : Kj j (L⟨ R ∪R R' ⟩) ≃ Kj j (G⟨ j , R ∪R R' ⟩)
    kl'≃km : Kj j (L⟨ R ∪R R' ⟩) ≃ Kj j (M⟨ j , R ⟩)
    km≃km' : Kj j (M⟨ j , R ⟩) ≃ Kj j (M⟨ j , R ∪R R' ⟩)

case4
  : ∀ {j R R'}
  → Expansive j R
  → (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩)
  → (L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩)
  → (G⟨ j , R ∪R R' ⟩ ⊆ L⟨ R ∪R R' ⟩)
  → (∀ {r} → R' r → RuleHoldsIn r (M⟨ j , R ⟩))
  → Case4 j R R'
case4 {j} {R} {R'} e g⊆l' l'⊆m g'⊆l' adm =
  record
    { common = case1 e

    ; l'≃g' = l'⊆g' , g'⊆l'
    ; m≃m' = lift-M (λ rr → inl rr) , m'⊆m adm

    ; m≃kl' = m⊆kl' , kl'⊆m
    ; kg≃kl' = kg⊆kl' , kl'⊆kg
    ; kl'≃kg' = (λ d → l'⊆g' d) , (λ d → g'⊆l' d)
    ; kl'≃km = kl'⊆km , km⊆kl'
    ; km≃km' =
        (λ d → lift-M (λ rr → inl rr) d)
        ,
        (λ d → m'⊆m adm d)
    }
  where
  l'⊆g' : L⟨ R ∪R R' ⟩ ⊆ G⟨ j , R ∪R R' ⟩
  l'⊆g' = lift-base-into-G

  kl'⊆m : Kj j (L⟨ R ∪R R' ⟩) ⊆ M⟨ j , R ⟩
  kl'⊆m = from (theorem1-3 {R' = R'} e) l'⊆m

  m⊆kl' : M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩)
  m⊆kl' = from (theorem1-4 {R' = R'} e) g⊆l'

  kg⊆kl' : Kj j (G⟨ j , R ⟩) ⊆ Kj j (L⟨ R ∪R R' ⟩)
  kg⊆kl' d = g⊆l' d

  kl'⊆kg : Kj j (L⟨ R ∪R R' ⟩) ⊆ Kj j (G⟨ j , R ⟩)
  kl'⊆kg d = kjM⊆kjG e (m⊆km e (kl'⊆m d))

  kl'⊆km : Kj j (L⟨ R ∪R R' ⟩) ⊆ Kj j (M⟨ j , R ⟩)
  kl'⊆km d = m⊆km e (kl'⊆m d)

  km⊆kl' : Kj j (M⟨ j , R ⟩) ⊆ Kj j (L⟨ R ∪R R' ⟩)
  km⊆kl' d = m⊆kl' (km⊆m d)

record Case5 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'

    l'≃kl' : L⟨ R ∪R R' ⟩ ≃ Kj j (L⟨ R ∪R R' ⟩)
    l'≃g' : L⟨ R ∪R R' ⟩ ≃ G⟨ j , R ∪R R' ⟩
    g'≃m' : G⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ∪R R' ⟩

    kl'≃kg' : Kj j (L⟨ R ∪R R' ⟩) ≃ Kj j (G⟨ j , R ∪R R' ⟩)
    kg'≃km' : Kj j (G⟨ j , R ∪R R' ⟩) ≃ Kj j (M⟨ j , R ∪R R' ⟩)

case5
  : ∀ {j R R'}
  → Expansive j R
  → (M⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩)
  → (G⟨ j , R ∪R R' ⟩ ⊆ L⟨ R ∪R R' ⟩)
  → (M⟨ j , R ∪R R' ⟩ ⊆ L⟨ R ∪R R' ⟩)
  → Case5 j R R'
case5 {j} {R} {R'} e m⊆l' g'⊆l' m'⊆l' =
  record
    { common = case1 e

    ; l'≃kl' = l'⊆kl' , kl'⊆l'
    ; l'≃g' = l'⊆g' , g'⊆l'
    ; g'≃m' = g'⊆m' , m'⊆g'

    ; kl'≃kg' = (λ d → l'⊆g' d) , (λ d → g'⊆l' d)
    ; kg'≃km' = (λ d → g'⊆m' d) , (λ d → m'⊆g' d)
    }
  where
  e' : Expansive j (R ∪R R')
  e' = mkExpansive (lift-Expansive e inj₁)

  l'⊆kl' : L⟨ R ∪R R' ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩)
  l'⊆kl' = theorem1-1 {R' = R'} e

  kl'⊆l' : Kj j (L⟨ R ∪R R' ⟩) ⊆ L⟨ R ∪R R' ⟩
  kl'⊆l' = from (theorem1-2 {R' = R'} e) m⊆l'

  l'⊆g' : L⟨ R ∪R R' ⟩ ⊆ G⟨ j , R ∪R R' ⟩
  l'⊆g' = lift-base-into-G

  g'⊆m' : G⟨ j , R ∪R R' ⟩ ⊆ M⟨ j , R ∪R R' ⟩
  g'⊆m' = g⊆m e'

  m'⊆g' : M⟨ j , R ∪R R' ⟩ ⊆ G⟨ j , R ∪R R' ⟩
  m'⊆g' d = l'⊆g' (m'⊆l' d)

record Case6 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'
    l'≃l : L⟨ R ∪R R' ⟩ ≃ L⟨ R ⟩
    kl'≃kl : Kj j (L⟨ R ∪R R' ⟩) ≃ Kj j (L⟨ R ⟩)

case6
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ≃ L⟨ R ⟩)
  → Case6 j R R'
case6 {j} e l'≃l =
  record
    { common = case1 e
    ; l'≃l = l'≃l
    ; kl'≃kl = (λ d → fst l'≃l d) , (λ d → snd l'≃l d)
    }

record Case7 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'

    l'≃g : L⟨ R ∪R R' ⟩ ≃ G⟨ j , R ⟩
    g'≃g : G⟨ j , R ∪R R' ⟩ ≃ G⟨ j , R ⟩
    m'≃m : M⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ⟩

    kl'≃kg : Kj j (L⟨ R ∪R R' ⟩) ≃ Kj j (G⟨ j , R ⟩)
    kg'≃kg : Kj j (G⟨ j , R ∪R R' ⟩) ≃ Kj j (G⟨ j , R ⟩)
    km'≃km : Kj j (M⟨ j , R ∪R R' ⟩) ≃ Kj j (M⟨ j , R ⟩)

case7
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ≃ G⟨ j , R ⟩)
  → (G⟨ j , R ∪R R' ⟩ ≃ G⟨ j , R ⟩)
  → (M⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ⟩)
  → Case7 j R R'
case7 {j} e l'≃g g'≃g m'≃m =
  record
    { common = case1 e

    ; l'≃g = l'≃g
    ; g'≃g = g'≃g
    ; m'≃m = m'≃m

    ; kl'≃kg = (λ d → fst l'≃g d) , (λ d → snd l'≃g d)
    ; kg'≃kg = (λ d → fst g'≃g d) , (λ d → snd g'≃g d)
    ; km'≃km = (λ d → fst m'≃m d) , (λ d → snd m'≃m d)
    }

record Case8 (j : S → S) (R R' : RuleSet) : Type ℓ where
  field
    common : Case1 j R R'

    l'≃m : L⟨ R ∪R R' ⟩ ≃ M⟨ j , R ⟩
    g'≃m : G⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ⟩
    m'≃m : M⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ⟩

    kl'≃km : Kj j (L⟨ R ∪R R' ⟩) ≃ Kj j (M⟨ j , R ⟩)
    kg'≃km : Kj j (G⟨ j , R ∪R R' ⟩) ≃ Kj j (M⟨ j , R ⟩)
    km'≃km : Kj j (M⟨ j , R ∪R R' ⟩) ≃ Kj j (M⟨ j , R ⟩)

case8
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ≃ M⟨ j , R ⟩)
  → (G⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ⟩)
  → (M⟨ j , R ∪R R' ⟩ ≃ M⟨ j , R ⟩)
  → Case8 j R R'
case8 {j} e l'≃m g'≃m m'≃m =
  record
    { common = case1 e

    ; l'≃m = l'≃m
    ; g'≃m = g'≃m
    ; m'≃m = m'≃m

    ; kl'≃km = (λ d → fst l'≃m d) , (λ d → snd l'≃m d)
    ; kg'≃km = (λ d → fst g'≃m d) , (λ d → snd g'≃m d)
    ; km'≃km = (λ d → fst m'≃m d) , (λ d → snd m'≃m d)
    }
