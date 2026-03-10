open import Cubical.Core.Primitives

module Substructural.Core.Conservation {ℓ} (S : Type ℓ) where

open import Substructural.Prelude
open import Substructural.Core.Judgement S
open import Substructural.Core.Rules S
open import Substructural.Core.Derivation S
open import Substructural.Core.Nucleus S
open import Substructural.Core.Extensions S
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)

-- Section 2 optional structural rule Comm (exchange).
Comm : RuleSchema
Comm L =
  ∀ {U₁ U₂ a₁ a₂ b}
  → L (U₁ ++ (a₁ ∷ a₂ ∷ U₂)) b
  → L (U₁ ++ (a₂ ∷ a₁ ∷ U₂)) b

Mono : RuleSchema
Mono L =
  ∀ {U₁ U₂ a b}
  → L (U₁ ++ U₂) b
  → L (plug₁ U₁ a U₂) b

Contr : RuleSchema
Contr L =
  ∀ {U₁ U₂ a b}
  → L (U₁ ++ (a ∷ a ∷ U₂)) b
  → L (plug₁ U₁ a U₂) b

comm-from-rules : ∀ {R} → CommRules ⊆R R → Comm (Deriv R)
comm-from-rules i d = ByRule (i comm-instance) (d ∷ᵃ []ᵃ)

mono-from-rules : ∀ {R} → MonoRules ⊆R R → Mono (Deriv R)
mono-from-rules i d = ByRule (i mono-instance) (d ∷ᵃ []ᵃ)

contr-from-rules : ∀ {R} → ContrRules ⊆R R → Contr (Deriv R)
contr-from-rules i d = ByRule (i contr-instance) (d ∷ᵃ []ᵃ)

transportCtx
  : ∀ {L : Entailment} {Γ Γ' b}
  → Γ ≡ Γ'
  → L Γ b
  → L Γ' b
transportCtx {L = L} {b = b} p d = subst (λ X → L X b) p d

bubble-right
  : ∀ {L a b}
  → Comm L
  → (U V : Ctx)
  → L (U ++ (a ∷ V)) b
  → L (U ++ (V ++ (a ∷ []))) b
bubble-right c U [] d = d
bubble-right {L} {a} {b} c U (x ∷ V) d =
  transportCtx {L = L} {b = b} (++-assoc U (x ∷ []) (V ++ (a ∷ [])))
    (bubble-right {L = L} {a = a} {b = b} c (U ++ (x ∷ [])) V
      (transportCtx {L = L} {b = b} (sym (++-assoc U (x ∷ []) (a ∷ V)))
        (c {U₁ = U} {U₂ = V} {a₁ = a} {a₂ = x} d)))

bubble-left
  : ∀ {L a b}
  → Comm L
  → (U V : Ctx)
  → L (U ++ (V ++ (a ∷ []))) b
  → L (U ++ (a ∷ V)) b
bubble-left c U [] d = d
bubble-left {L} {a} {b} c U (x ∷ V) d =
  c {U₁ = U} {U₂ = V} {a₁ = x} {a₂ = a}
    (transportCtx {L = L} {b = b} (++-assoc U (x ∷ []) (a ∷ V))
      (bubble-left {L = L} {a = a} {b = b} c (U ++ (x ∷ [])) V
        (transportCtx {L = L} {b = b} (sym (++-assoc U (x ∷ []) (V ++ (a ∷ [])))) d)))

head→tail
  : ∀ {L a U b}
  → Comm L
  → L (prefix a U) b
  → L (suffix U a) b
head→tail {L} {a} {U} {b} c d = bubble-right {L = L} {a = a} {b = b} c [] U d

tail→head
  : ∀ {L a U b}
  → Comm L
  → L (suffix U a) b
  → L (prefix a U) b
tail→head {L} {a} {U} {b} c d = bubble-left {L = L} {a = a} {b = b} c [] U d

bi→left : ∀ {j L} → BiProgressive j L → LeftProgressive j L
bi→left n = mkLeftProgressive λ {U} {a} {b} d →
  BiProgressive.biProgressive n {U = U} {V = []} {a = a} {b = b} d

bi→right : ∀ {j L} → BiProgressive j L → RightProgressive j L
bi→right n = mkRightProgressive λ {U} {a} {b} d →
  BiProgressive.biProgressive n {U = []} {V = U} {a = a} {b = b} d

left→bi : ∀ {j L} → Comm L → LeftProgressive j L → BiProgressive j L
left→bi {j} {L} c n = mkBiProgressive liftL
  where
  liftL
    : ∀ {U V a b}
    → L (plug₁ U a V) (j b)
    → L (plug₁ U (j a) V) (j b)
  liftL {U} {V} {a} {b} d =
    bubble-left {L = L} {a = j a} {b = j b} c U V
      (transportCtx {L = L} {b = j b} (++-assoc U V ((j a) ∷ []))
        (LeftProgressive.leftProgressive n
          (transportCtx {L = L} {b = j b} (sym (++-assoc U V (a ∷ [])))
            (bubble-right {L = L} {a = a} {b = j b} c U V d))))

right→bi : ∀ {j L} → Comm L → RightProgressive j L → BiProgressive j L
right→bi {j} {L} c n = mkBiProgressive liftR
  where
  liftR
    : ∀ {U V a b}
    → L (plug₁ U a V) (j b)
    → L (plug₁ U (j a) V) (j b)
  liftR {U} {V} {a} {b} d =
    bubble-left {L = L} {a = j a} {b = j b} c U V
      (transportCtx {L = L} {b = j b} (++-assoc U V ((j a) ∷ []))
        (head→tail {L = L} {a = j a} {U = U ++ V} {b = j b} c
          (RightProgressive.rightProgressive n
            (tail→head {L = L} {a = a} {U = U ++ V} {b = j b} c
              (transportCtx {L = L} {b = j b} (sym (++-assoc U V (a ∷ [])))
                (bubble-right {L = L} {a = a} {b = j b} c U V d))))))

left↔right : ∀ {j L} → Comm L → LeftProgressive j L ↔ RightProgressive j L
left↔right {j} {L} c = intro toLR fromLR
  where
  toLR : LeftProgressive j L → RightProgressive j L
  toLR n = bi→right (left→bi c n)

  fromLR : RightProgressive j L → LeftProgressive j L
  fromLR n = bi→left (right→bi c n)

left↔bi : ∀ {j L} → Comm L → LeftProgressive j L ↔ BiProgressive j L
left↔bi {j} {L} c = intro toLB fromLB
  where
  toLB : LeftProgressive j L → BiProgressive j L
  toLB n = left→bi c n

  fromLB : BiProgressive j L → LeftProgressive j L
  fromLB = bi→left

right↔bi : ∀ {j L} → Comm L → RightProgressive j L ↔ BiProgressive j L
right↔bi {j} {L} c = intro toRB fromRB
  where
  toRB : RightProgressive j L → BiProgressive j L
  toRB n = right→bi c n

  fromRB : BiProgressive j L → RightProgressive j L
  fromRB = bi→right

lemma3-progressive
  : ∀ {j L}
  → (BiProgressive j L → LeftProgressive j L × RightProgressive j L)
  × (Comm L
  → (LeftProgressive j L ↔ RightProgressive j L)
    × (LeftProgressive j L ↔ BiProgressive j L)
    × (RightProgressive j L ↔ BiProgressive j L))
lemma3-progressive =
  (λ b → bi→left b , bi→right b)
  ,
  (λ c → left↔right c , left↔bi c , right↔bi c)

-- Lemma 3:
-- (1) bi-nucleus implies left and right nuclei,
-- (2) under Comm they are equivalent.
lemma3
  : ∀ {j L}
  → (BiNucleus j L → LeftNucleus j L × RightNucleus j L)
  × (Comm L
  → (LeftNucleus j L ↔ RightNucleus j L)
    × (LeftNucleus j L ↔ BiNucleus j L)
    × (RightNucleus j L ↔ BiNucleus j L))
lemma3 {j} {L} =
  (λ b →
      mkLeftNucleus (biNucleus-rj b)
        (LeftProgressive.leftProgressive
          (bi→left {j} {L} (mkBiProgressive {j} {L} (biNucleus-lj b))))
    ,
      mkRightNucleus (biNucleus-rj b)
        (RightProgressive.rightProgressive
          (bi→right {j} {L} (mkBiProgressive {j} {L} (biNucleus-lj b)))))
  ,
  (λ c →
      intro
        (λ l → mkRightNucleus (leftNucleus-rj l)
           (RightProgressive.rightProgressive
             (to (left↔right {j} {L} c)
               (mkLeftProgressive {j} {L} (leftNucleus-ljleft l)))))
        (λ r → mkLeftNucleus (rightNucleus-rj r)
           (LeftProgressive.leftProgressive
             (from (left↔right {j} {L} c)
               (mkRightProgressive {j} {L} (rightNucleus-ljright r)))))
    ,
      intro
        (λ l → mkBiNucleus (leftNucleus-rj l)
           (BiProgressive.biProgressive
             (to (left↔bi {j} {L} c)
               (mkLeftProgressive {j} {L} (leftNucleus-ljleft l)))))
        (λ b → mkLeftNucleus (biNucleus-rj b)
           (LeftProgressive.leftProgressive
             (from (left↔bi {j} {L} c)
               (mkBiProgressive {j} {L} (biNucleus-lj b)))))
    ,
      intro
        (λ r → mkBiNucleus (rightNucleus-rj r)
           (BiProgressive.biProgressive
             (to (right↔bi {j} {L} c)
               (mkRightProgressive {j} {L} (rightNucleus-ljright r)))))
        (λ b → mkRightNucleus (biNucleus-rj b)
           (RightProgressive.rightProgressive
             (from (right↔bi {j} {L} c)
               (mkBiProgressive {j} {L} (biNucleus-lj b)))))
  )

-- Lemma 6(1): Rj and Reflj are inter-derivable. L not inductively generated?
rj→reflj
  : ∀ {j R}
  → Rj j (L⟨ R ⟩)
  → Reflj j (L⟨ R ⟩)
rj→reflj ρ a = ρ Refl

reflj→rj
  : ∀ {j R}
  → Reflj j (L⟨ R ⟩)
  → Rj j (L⟨ R ⟩)
reflj→rj {j} {R} ρ {Γ} {a} d =
  transportCtx {L = L⟨ R ⟩} {b = j a} (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} d (ρ a))

-- Lemma 6(2): Lj and Transj are inter-derivable.
lj→transj
  : ∀ {j R}
  → Lj j (L⟨ R ⟩)
  → Transj j (L⟨ R ⟩)
lj→transj σ d₁ d₂ = Trans d₁ (σ d₂)

transj→lj
  : ∀ {j R}
  → Transj j (L⟨ R ⟩)
  → Lj j (L⟨ R ⟩)
transj→lj τ d = τ Refl d

-- Lemma 6(3): j-stab and Lj+ are inter-derivable.
jstab→lj+
  : ∀ {j R}
  → j-stab j (L⟨ R ⟩)
  → Lj+ j (L⟨ R ⟩)
jstab→lj+ {j} σ {U} {V} {a} {b} d = Trans {U = singleton (j a)} {V₁ = U} {V₂ = V} (σ a) d

lj+→jstab
  : ∀ {j R}
  → Lj+ j (L⟨ R ⟩)
  → j-stab j (L⟨ R ⟩)
lj+→jstab σ a = σ {U = []} {V = []} {a = a} {b = a} Refl

Rj-admissible : (S → S) → Entailment → Type ℓ
Rj-admissible j L = ∀ Γ a → RuleHoldsIn (mkRule ((Γ ▷ a) ∷ []) (Γ ▷ j a)) L

Reflj-admissible : (S → S) → Entailment → Type ℓ
Reflj-admissible j L = ∀ a → RuleHoldsIn (mkRule [] (singleton a ▷ j a)) L

Lj-admissible : (S → S) → Entailment → Type ℓ
Lj-admissible j L =
  ∀ U V a b
  → RuleHoldsIn (mkRule ((plug₁ U a V ▷ j b) ∷ []) (plug₁ U (j a) V ▷ j b)) L

Transj-admissible : (S → S) → Entailment → Type ℓ
Transj-admissible j L =
  ∀ W U V a b
  → RuleHoldsIn
      (mkRule ((W ▷ j a) ∷ (plug₁ U a V ▷ j b) ∷ []) (plug U V W ▷ j b))
      L

jstab-admissible : (S → S) → Entailment → Type ℓ
jstab-admissible j L = ∀ a → RuleHoldsIn (mkRule [] (singleton (j a) ▷ a)) L

Lj+-admissible : (S → S) → Entailment → Type ℓ
Lj+-admissible j L =
  ∀ U V a b
  → RuleHoldsIn (mkRule ((plug₁ U a V ▷ b) ∷ []) (plug₁ U (j a) V ▷ b)) L

rj-adm→reflj-adm
  : ∀ {j R}
  → Rj-admissible j (L⟨ R ⟩)
  → Reflj-admissible j (L⟨ R ⟩)
rj-adm→reflj-adm ρ a _ = ρ (singleton a) a (Refl ∷ᵃ []ᵃ)

reflj-adm→rj-adm
  : ∀ {j R}
  → Reflj-admissible j (L⟨ R ⟩)
  → Rj-admissible j (L⟨ R ⟩)
reflj-adm→rj-adm {j} {R} ρ Γ a (d ∷ᵃ []ᵃ) =
  transportCtx {L = L⟨ R ⟩} {b = j a} (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} d (ρ a []ᵃ))

lj-adm→transj-adm
  : ∀ {j R}
  → Lj-admissible j (L⟨ R ⟩)
  → Transj-admissible j (L⟨ R ⟩)
lj-adm→transj-adm σ W U V a b (d₁ ∷ᵃ d₂ ∷ᵃ []ᵃ) =
  Trans d₁ (σ U V a b (d₂ ∷ᵃ []ᵃ))

transj-adm→lj-adm
  : ∀ {j R}
  → Transj-admissible j (L⟨ R ⟩)
  → Lj-admissible j (L⟨ R ⟩)
transj-adm→lj-adm {j} τ U V a b (d ∷ᵃ []ᵃ) =
  τ (singleton (j a)) U V a b (Refl ∷ᵃ d ∷ᵃ []ᵃ)

jstab-adm→lj+-adm
  : ∀ {j R}
  → jstab-admissible j (L⟨ R ⟩)
  → Lj+-admissible j (L⟨ R ⟩)
jstab-adm→lj+-adm {j} σ U V a b (d ∷ᵃ []ᵃ) =
  Trans {U = singleton (j a)} {V₁ = U} {V₂ = V}
    (σ a []ᵃ)
    d

lj+-adm→jstab-adm
  : ∀ {j R}
  → Lj+-admissible j (L⟨ R ⟩)
  → jstab-admissible j (L⟨ R ⟩)
lj+-adm→jstab-adm σ a _ = σ [] [] a a (Refl ∷ᵃ []ᵃ)

-- Lemma 6 (derivable-form).
remark1
  : ∀ {j R}
  → (Rj j (L⟨ R ⟩) ↔ Reflj j (L⟨ R ⟩))
  × (Lj j (L⟨ R ⟩) ↔ Transj j (L⟨ R ⟩))
  × (j-stab j (L⟨ R ⟩) ↔ Lj+ j (L⟨ R ⟩))
remark1 =
  intro rj→reflj reflj→rj
  , intro lj→transj transj→lj
  , intro jstab→lj+ lj+→jstab

-- Remark 1 (admissible-form), kept explicit as a separate theorem.
remark1-admissible
  : ∀ {j R}
  → (Rj-admissible j (L⟨ R ⟩) ↔ Reflj-admissible j (L⟨ R ⟩))
  × (Lj-admissible j (L⟨ R ⟩) ↔ Transj-admissible j (L⟨ R ⟩))
  × (jstab-admissible j (L⟨ R ⟩) ↔ Lj+-admissible j (L⟨ R ⟩))
remark1-admissible =
  intro rj-adm→reflj-adm reflj-adm→rj-adm
  , intro lj-adm→transj-adm transj-adm→lj-adm
  , intro jstab-adm→lj+-adm lj+-adm→jstab-adm

-- Internal support package collecting the expansive-core facts used below.
expansiveCoreFacts
  : ∀ {j R}
  → Expansive j R
  → (L⟨ R ⟩ ⊆ G⟨ j , R ⟩)
    × (L⟨ R ⟩ ⊆ M⟨ j , R ⟩)
    × BiNucleus j (G⟨ j , R ⟩)
    × BiNucleus j (M⟨ j , R ⟩)
    × ((∀ {R'} → R ⊆R R' → G⟨ j , R ⟩ ⊆ G⟨ j , R' ⟩)
      × (∀ {R'} → R ⊆R R' → M⟨ j , R ⟩ ⊆ M⟨ j , R' ⟩))
expansiveCoreFacts {j} {R} e =
  lift-base-into-G
  , lift-base-into-M
  , mkBiNucleus
      (lift-Expansive e (λ rr → inl rr))
      (BiProgressive.biProgressive bi-on-G)
  , mkBiNucleus
      (lift-Expansive e (λ rr → inl rr))
      (BiProgressive.biProgressive bi-on-M)
  , (lift-G , lift-M)

premises-⊆
  : ∀ {L L' : Entailment} {ps : List Seq}
  → L ⊆ L'
  → PremisesHold L ps
  → PremisesHold L' ps
premises-⊆ {ps = []} i []ᵃ = []ᵃ
premises-⊆ {ps = p ∷ ps} i (d ∷ᵃ ds) = i d ∷ᵃ premises-⊆ i ds

-- Numbering note: `expansiveCoreFacts` above is the project-local package used by existing
-- code. The lemmas below use the paper numbering (8.1, 8.3, 8.4, 8.5).

mutual

  g⊆base-from-lj+survives-all
    : ∀ {j R ps}
    → Lj j (L⟨ R ⟩)
    → (∀ {r} → R r → SurvivesAfter j r R)
    → PremisesHold (G⟨ j , R ⟩) ps
    → PremisesHold (L⟨ R ⟩) ps
  g⊆base-from-lj+survives-all {ps = []} lj surv []ᵃ = []ᵃ
  g⊆base-from-lj+survives-all {ps = p ∷ ps} lj surv (d ∷ᵃ ds) =
    g⊆base-from-lj+survives lj surv d ∷ᵃ g⊆base-from-lj+survives-all lj surv ds

  g⊆base-from-lj+survives
    : ∀ {j R}
    → Lj j (L⟨ R ⟩)
    → (∀ {r} → R r → SurvivesAfter j r R)
    → G⟨ j , R ⟩ ⊆ L⟨ R ⟩
  g⊆base-from-lj+survives lj surv Refl = Refl
  g⊆base-from-lj+survives lj surv (Trans d d₁) = Trans (g⊆base-from-lj+survives lj surv d) (g⊆base-from-lj+survives lj surv d₁)
  g⊆base-from-lj+survives lj surv (ByRule (inl rr) ds) = ByRule rr (g⊆base-from-lj+survives-all lj surv ds)
  g⊆base-from-lj+survives lj surv (ByRule (inr (inl lj-instance)) ds) =
    lj (All-lookup-head (g⊆base-from-lj+survives-all lj surv ds))
  g⊆base-from-lj+survives lj surv (ByRule (inr (inr (rj-instance rr))) ds) =
    surv rr (g⊆base-from-lj+survives-all lj surv ds)

lj+survives-from-g⊆base
  : ∀ {j R}
  → G⟨ j , R ⟩ ⊆ L⟨ R ⟩
  → Lj j (L⟨ R ⟩) × (∀ {r} → R r → SurvivesAfter j r R)
lj+survives-from-g⊆base {j} {R} g⊆l =
  ljL , surv
  where
  ljL : Lj j (L⟨ R ⟩)
  ljL {U} {V} {a} {b} d = g⊆l (embed-Lj (lift-base-into-G d))

  surv : ∀ {r} → R r → SurvivesAfter j r R
  surv {r} rr ds =
    g⊆l (ByRule (inr (inr (rj-instance rr))) (premises-⊆ lift-base-into-G ds))

g⊆base↔lj+survives
  : ∀ {j R}
  → (Lj j (L⟨ R ⟩) × (∀ {r} → R r → SurvivesAfter j r R)
    → G⟨ j , R ⟩ ⊆ L⟨ R ⟩)
    × (G⟨ j , R ⟩ ⊆ L⟨ R ⟩
      → Lj j (L⟨ R ⟩) × (∀ {r} → R r → SurvivesAfter j r R))
g⊆base↔lj+survives =
  (λ { (lj , surv) → g⊆base-from-lj+survives lj surv })
  , lj+survives-from-g⊆base

mutual

  g⊆deriv-R∪Rj-all
    : ∀ {j R ps}
    → BiProgressiveR j R
    → PremisesHold (G⟨ j , R ⟩) ps
    → PremisesHold (Deriv (R ∪R RjRules j R)) ps
  g⊆deriv-R∪Rj-all {ps = []} bn []ᵃ = []ᵃ
  g⊆deriv-R∪Rj-all {ps = p ∷ ps} bn (d ∷ᵃ ds) =
    g⊆deriv-R∪Rj bn d ∷ᵃ g⊆deriv-R∪Rj-all bn ds

  g⊆deriv-R∪Rj
    : ∀ {j R}
    → BiProgressiveR j R
    → G⟨ j , R ⟩ ⊆ Deriv (R ∪R RjRules j R)
  g⊆deriv-R∪Rj bn Refl = Refl
  g⊆deriv-R∪Rj bn (Trans d d₁) = Trans (g⊆deriv-R∪Rj bn d) (g⊆deriv-R∪Rj bn d₁)
  g⊆deriv-R∪Rj bn (ByRule (inl rr) ds) = ByRule (inl rr) (g⊆deriv-R∪Rj-all bn ds)
  g⊆deriv-R∪Rj {j} {R} bn (ByRule (inr (inl lj-instance)) ds) =
    lift-BiProgressiveR bn (λ rr → inl rr) (All-lookup-head (g⊆deriv-R∪Rj-all bn ds))
  g⊆deriv-R∪Rj bn (ByRule (inr (inr (rj-instance rr))) ds) =
    ByRule (inr (rj-instance rr)) (g⊆deriv-R∪Rj-all bn ds)

deriv-R∪Rj⊆g
  : ∀ {j R}
  → Deriv (R ∪R RjRules j R) ⊆ G⟨ j , R ⟩
deriv-R∪Rj⊆g {j} {R} = lift-⊆R embed
  where
  embed : (R ∪R RjRules j R) ⊆R GjRules j R
  embed (inl rr) = inl rr
  embed (inr (rj-instance rr)) = inr (inr (rj-instance rr))

g↔deriv-R∪Rj
  : ∀ {j R}
  → BiProgressiveR j R
  → (G⟨ j , R ⟩ ⊆ Deriv (R ∪R RjRules j R))
    × (Deriv (R ∪R RjRules j R) ⊆ G⟨ j , R ⟩)
g↔deriv-R∪Rj bn = g⊆deriv-R∪Rj bn , deriv-R∪Rj⊆g

kj-refl
  : ∀ {j R}
  → Rj j (L⟨ R ⟩)
  → ∀ {a} → Kj j (L⟨ R ⟩) (singleton a) a
kj-refl rj = rj Refl

remark3
  : ∀ {j R}
  → Lj j (L⟨ R ⟩)
  → ∀ {U V₁ V₂ a b}
  → Kj j (L⟨ R ⟩) U a
  → Kj j (L⟨ R ⟩) (plug₁ V₁ a V₂) b
  → Kj j (L⟨ R ⟩) (plug V₁ V₂ U) b
remark3 lj d₁ d₂ = Trans d₁ (lj d₂)

kj-lj-adm
  : ∀ {j R}
  → Lj j (L⟨ R ⟩)
  → Lj j (Kj j (L⟨ R ⟩))
kj-lj-adm lj d = lj d

kj-rj-adm
  : ∀ {j R}
  → Rj j (L⟨ R ⟩)
  → Rj j (Kj j (L⟨ R ⟩))
kj-rj-adm rj d = rj d

kj-nucleus-facts
  : ∀ {j R}
  → Nucleus j (L⟨ R ⟩)
  → (∀ {a} → Kj j (L⟨ R ⟩) (singleton a) a)
    × (∀ {U V₁ V₂ a b}
      → Kj j (L⟨ R ⟩) U a
      → Kj j (L⟨ R ⟩) (plug₁ V₁ a V₂) b
      → Kj j (L⟨ R ⟩) (plug V₁ V₂ U) b)
    × Lj j (Kj j (L⟨ R ⟩))
    × Rj j (Kj j (L⟨ R ⟩))
kj-nucleus-facts n =
  kj-refl (nucleus-rj n)
  , remark3 (nucleus-lj n)
  , kj-lj-adm (nucleus-lj n)
  , kj-rj-adm (nucleus-rj n)

kj-comm : ∀ {j L} → Comm L → Comm (Kj j L)
kj-comm c d = c d

kj-mono : ∀ {j L} → Mono L → Mono (Kj j L)
kj-mono m d = m d

kj-contr : ∀ {j L} → Contr L → Contr (Kj j L)
kj-contr c d = c d

comm-in-G : ∀ {j R} → CommRules ⊆R R → Comm (G⟨ j , R ⟩)
comm-in-G i = comm-from-rules (λ cr → inl (i cr))

mono-in-G : ∀ {j R} → MonoRules ⊆R R → Mono (G⟨ j , R ⟩)
mono-in-G i = mono-from-rules (λ mr → inl (i mr))

contr-in-G : ∀ {j R} → ContrRules ⊆R R → Contr (G⟨ j , R ⟩)
contr-in-G i = contr-from-rules (λ cr → inl (i cr))

comm-in-M : ∀ {j R} → CommRules ⊆R R → Comm (M⟨ j , R ⟩)
comm-in-M i = comm-from-rules (λ cr → inl (i cr))

mono-in-M : ∀ {j R} → MonoRules ⊆R R → Mono (M⟨ j , R ⟩)
mono-in-M i = mono-from-rules (λ mr → inl (i mr))

contr-in-M : ∀ {j R} → ContrRules ⊆R R → Contr (M⟨ j , R ⟩)
contr-in-M i = contr-from-rules (λ cr → inl (i cr))

destab-mapSuccAll
  : ∀ {j R ps}
  → PremisesHold (M⟨ j , R ⟩) (map (mapSucc j) ps)
  → PremisesHold (M⟨ j , R ⟩) ps
destab-mapSuccAll {ps = []} []ᵃ = []ᵃ
destab-mapSuccAll {j} {R} {ps = p ∷ ps} (d ∷ᵃ ds) =
  destab-M {j = j} {R = R} d ∷ᵃ destab-mapSuccAll ds

-- Core internal step for Proposition 1: Gj(L) ⊆ Mj(L).
mutual
  g⊆m-all
    : ∀ {j R ps}
    → Expansive j R
    → PremisesHold (G⟨ j , R ⟩) ps
    → PremisesHold (M⟨ j , R ⟩) ps
  g⊆m-all {ps = []} e []ᵃ = []ᵃ
  g⊆m-all {ps = p ∷ ps} e (d ∷ᵃ ds) = g⊆m e d ∷ᵃ g⊆m-all e ds

  g⊆m
    : ∀ {j R}
    → Expansive j R
    → G⟨ j , R ⟩ ⊆ M⟨ j , R ⟩
  g⊆m e Refl = Refl
  g⊆m e (Trans d d₁) = Trans (g⊆m e d) (g⊆m e d₁)
  g⊆m {j} {R} e (ByRule (inl rr) ds) = ByRule (inl rr) (g⊆m-all e ds)
  g⊆m {j} {R} e (ByRule (inr (inl lj-instance)) ds) =
    jstab→lj+ {j = j} {R = MjRules j R}
      (λ a → jstab-in-M {j = j} {R = R} {a = a})
      (All-lookup-head (g⊆m-all e ds))
  g⊆m {j} {R} e (ByRule (inr (inr (rj-instance rr))) ds) =
    raise-M-from-expansive {j = j} {R = R} e
      (ByRule (inl rr) (destab-mapSuccAll (g⊆m-all e ds)))

kj⊆m
  : ∀ {j R}
  → Kj j (L⟨ R ⟩) ⊆ M⟨ j , R ⟩
kj⊆m {j} {R} {Γ} {a} d =
  destab-M {j = j} {R = R} (lift-base-into-M {j = j} {R = R} d)

mutual

  m→gj-all
    : ∀ {j R ps}
    → Expansive j R
    → PremisesHold (M⟨ j , R ⟩) ps
    → PremisesHold (G⟨ j , R ⟩) (map (mapSucc j) ps)
  m→gj-all {ps = []} e []ᵃ = []ᵃ
  m→gj-all {j} {R} {ps = p ∷ ps} e (d ∷ᵃ ds) = m→gj e d ∷ᵃ m→gj-all e ds

  m→gj
    : ∀ {j R Γ a}
    → Expansive j R
    → M⟨ j , R ⟩ Γ a
    → G⟨ j , R ⟩ Γ (j a)
  m→gj e Refl = lift-Expansive e (λ rr → inl rr) Refl
  m→gj e (Trans d d₁) = Trans (m→gj e d) (embed-Lj (m→gj e d₁))
  m→gj e (ByRule (inl rr) ds) = ByRule (inr (inr (rj-instance rr))) (m→gj-all e ds)
  m→gj e (ByRule (inr jstab-instance) ds) = Refl

-- Proposition 1: four inclusions proved internally.
proposition1
  : ∀ {j R}
  → Expansive j R
  → (L⟨ R ⟩ ⊆ Kj j (L⟨ R ⟩))
    × (L⟨ R ⟩ ⊆ G⟨ j , R ⟩)
    × (G⟨ j , R ⟩ ⊆ M⟨ j , R ⟩)
    × (Kj j (L⟨ R ⟩) ⊆ M⟨ j , R ⟩)
proposition1 {j} {R} e with expansiveCoreFacts {j} {R} e
... | l⊆g , _ , _ , _ , _ =
  onBase-Expansive e , l⊆g , g⊆m e , kj⊆m

-- Theorem 1 (Conservation), clauses (1)-(4).
theorem1
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩))
    × ((Kj j (L⟨ R ∪R R' ⟩) ⊆ L⟨ R ∪R R' ⟩) ↔ (M⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩))
    × ((Kj j (L⟨ R ∪R R' ⟩) ⊆ M⟨ j , R ⟩) ↔ (L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩))
    × ((M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩)) ↔ (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩))
theorem1 {j} {R} {R'} e =
  l'⊆k
  , intro c2-to c2-from
  , intro c3-to c3-from
  , intro c4-to c4-from
  where
  L' : Entailment
  L' = L⟨ R ∪R R' ⟩

  K' : Entailment
  K' = Kj j L'

  M : Entailment
  M = M⟨ j , R ⟩

  G : Entailment
  G = G⟨ j , R ⟩

  l'⊆k : L' ⊆ K'
  l'⊆k = lift-Expansive e (λ rr → inl rr)

  c2-to : K' ⊆ L' → M ⊆ L'
  c2-to k⊆l' = m→l'
    where
    jstabL' : ∀ a → L' (singleton (j a)) a
    jstabL' a = k⊆l' {Γ = singleton (j a)} {a = a} Refl

    mutual

      m→l'-all
        : ∀ {ps}
        → PremisesHold M ps
        → PremisesHold L' ps
      m→l'-all {ps = []} []ᵃ = []ᵃ
      m→l'-all {ps = p ∷ ps} (d ∷ᵃ ds) = m→l' d ∷ᵃ m→l'-all ds

      m→l' : M ⊆ L'
      m→l' Refl = Refl
      m→l' (Trans d d₁) = Trans (m→l' d) (m→l' d₁)
      m→l' (ByRule (inl rr) ds) = ByRule (inl rr) (m→l'-all ds)
      m→l' (ByRule (inr jstab-instance) ds) = jstabL' _

  c2-from : M ⊆ L' → K' ⊆ L'
  c2-from m⊆l' {Γ} {a} d =
    transportCtx {L = L'} {b = a} (++-unit-r Γ)
      (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = j a} {b = a} d (m⊆l' jstab-in-M))

  c3-to : K' ⊆ M → L' ⊆ M
  c3-to k⊆m d = k⊆m (l'⊆k d)

  c3-from : L' ⊆ M → K' ⊆ M
  c3-from l'⊆m d = destab-M (l'⊆m d)

  c4-to : M ⊆ K' → G ⊆ L'
  c4-to m⊆k = g→l'
    where
    g⊆k : G ⊆ K'
    g⊆k d = m⊆k (g⊆m e d)

    jj→j : ∀ b → L' (singleton (j (j b))) (j b)
    jj→j b = m⊆k d
      where
      lj+M
        : Lj+ j M
      lj+M = jstab→lj+ {j = j} {R = MjRules j R} (λ a → jstab-in-M {j = j} {R = R} {a = a})

      d : M (singleton (j (j b))) b
      d = lj+M {U = []} {V = []} {a = j b} {b = b} jstab-in-M

    mutual

      g→l'-all
        : ∀ {ps}
        → PremisesHold G ps
        → PremisesHold L' ps
      g→l'-all {ps = []} []ᵃ = []ᵃ
      g→l'-all {ps = p ∷ ps} (d ∷ᵃ ds) = g→l' d ∷ᵃ g→l'-all ds

      g→l' : G ⊆ L'
      g→l' Refl = Refl
      g→l' (Trans d d₁) = Trans (g→l' d) (g→l' d₁)
      g→l' (ByRule (inl rr) ds) = ByRule (inl rr) (g→l'-all ds)
      g→l' {Γ} d@(ByRule (inr (inl (lj-instance {b = b}))) ds) =
        transportCtx {L = L'} {b = j b} (++-unit-r Γ)
          (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = j (j b)} {b = j b} (g⊆k d) (jj→j b))
      g→l' {Γ} d@(ByRule (inr (inr (rj-instance {r = r} rr))) ds) =
        transportCtx {L = L'} {b = j (Seq.obj (conclusion r))} (++-unit-r Γ)
          (Trans {U = Γ} {V₁ = []} {V₂ = []}
            {a = j (j (Seq.obj (conclusion r)))}
            {b = j (Seq.obj (conclusion r))}
            (g⊆k d)
            (jj→j (Seq.obj (conclusion r))))

  c4-from : G ⊆ L' → M ⊆ K'
  c4-from g⊆l' d = g⊆l' (m→gj e d)
