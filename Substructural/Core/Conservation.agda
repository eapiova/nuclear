{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

module Substructural.Core.Conservation {ℓ} (S : Set ℓ) where

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

bi→left : ∀ {j L} → BiNucleus j L → LeftNucleus j L
bi→left n = mkLeftNucleus λ {U} {a} {b} d →
  BiNucleus.biNucleus n {U = U} {V = []} {a = a} {b = b} d

bi→right : ∀ {j L} → BiNucleus j L → RightNucleus j L
bi→right n = mkRightNucleus λ {U} {a} {b} d →
  BiNucleus.biNucleus n {U = []} {V = U} {a = a} {b = b} d

left→bi : ∀ {j L} → Comm L → LeftNucleus j L → BiNucleus j L
left→bi {j} {L} c n = mkBiNucleus liftL
  where
  liftL
    : ∀ {U V a b}
    → L (plug₁ U a V) (j b)
    → L (plug₁ U (j a) V) (j b)
  liftL {U} {V} {a} {b} d =
    bubble-left {L = L} {a = j a} {b = j b} c U V
      (transportCtx {L = L} {b = j b} (++-assoc U V ((j a) ∷ []))
        (LeftNucleus.leftNucleus n
          (transportCtx {L = L} {b = j b} (sym (++-assoc U V (a ∷ [])))
            (bubble-right {L = L} {a = a} {b = j b} c U V d))))

right→bi : ∀ {j L} → Comm L → RightNucleus j L → BiNucleus j L
right→bi {j} {L} c n = mkBiNucleus liftR
  where
  liftR
    : ∀ {U V a b}
    → L (plug₁ U a V) (j b)
    → L (plug₁ U (j a) V) (j b)
  liftR {U} {V} {a} {b} d =
    bubble-left {L = L} {a = j a} {b = j b} c U V
      (transportCtx {L = L} {b = j b} (++-assoc U V ((j a) ∷ []))
        (head→tail {L = L} {a = j a} {U = U ++ V} {b = j b} c
          (RightNucleus.rightNucleus n
            (tail→head {L = L} {a = a} {U = U ++ V} {b = j b} c
              (transportCtx {L = L} {b = j b} (sym (++-assoc U V (a ∷ [])))
                (bubble-right {L = L} {a = a} {b = j b} c U V d))))))

left↔right : ∀ {j L} → Comm L → LeftNucleus j L ↔ RightNucleus j L
left↔right {j} {L} c = intro toLR fromLR
  where
  toLR : LeftNucleus j L → RightNucleus j L
  toLR n = bi→right (left→bi c n)

  fromLR : RightNucleus j L → LeftNucleus j L
  fromLR n = bi→left (right→bi c n)

left↔bi : ∀ {j L} → Comm L → LeftNucleus j L ↔ BiNucleus j L
left↔bi {j} {L} c = intro toLB fromLB
  where
  toLB : LeftNucleus j L → BiNucleus j L
  toLB n = left→bi c n

  fromLB : BiNucleus j L → LeftNucleus j L
  fromLB = bi→left

right↔bi : ∀ {j L} → Comm L → RightNucleus j L ↔ BiNucleus j L
right↔bi {j} {L} c = intro toRB fromRB
  where
  toRB : RightNucleus j L → BiNucleus j L
  toRB n = right→bi c n

  fromRB : BiNucleus j L → RightNucleus j L
  fromRB = bi→right

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
lemma3 =
  (λ b → bi→left b , bi→right b)
  ,
  (λ c → left↔right c , left↔bi c , right↔bi c)

-- Proposition 4: base entailment embeds into any rule-set extension.
proposition4
  : ∀ {R R'}
  → L⟨ R ⟩ ⊆ L⟨ R ∪R R' ⟩
proposition4 = lift-⊆R inj₁

-- Lemma 6(1): Rj and Reflj are inter-derivable.
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
Rj-admissible j L = ∀ Γ a → AdmissibleRule (mkRule ((Γ ▷ a) ∷ []) (Γ ▷ j a)) L

Reflj-admissible : (S → S) → Entailment → Type ℓ
Reflj-admissible j L = ∀ a → AdmissibleRule (mkRule [] (singleton a ▷ j a)) L

Lj-admissible : (S → S) → Entailment → Type ℓ
Lj-admissible j L =
  ∀ U V a b
  → AdmissibleRule (mkRule ((plug₁ U a V ▷ j b) ∷ []) (plug₁ U (j a) V ▷ j b)) L

Transj-admissible : (S → S) → Entailment → Type ℓ
Transj-admissible j L =
  ∀ W U V a b
  → AdmissibleRule
      (mkRule ((W ▷ j a) ∷ (plug₁ U a V ▷ j b) ∷ []) (plug U V W ▷ j b))
      L

jstab-admissible : (S → S) → Entailment → Type ℓ
jstab-admissible j L = ∀ a → AdmissibleRule (mkRule [] (singleton (j a) ▷ a)) L

Lj+-admissible : (S → S) → Entailment → Type ℓ
Lj+-admissible j L =
  ∀ U V a b
  → AdmissibleRule (mkRule ((plug₁ U a V ▷ b) ∷ []) (plug₁ U (j a) V ▷ b)) L

rj-adm→reflj-adm
  : ∀ {j R}
  → Rj-admissible j (L⟨ R ⟩)
  → Reflj-admissible j (L⟨ R ⟩)
rj-adm→reflj-adm ρ a = mkAdmissibleRule λ _ →
  AdmissibleRule.admit (ρ (singleton a) a) (Refl ∷ᵃ []ᵃ)

reflj-adm→rj-adm
  : ∀ {j R}
  → Reflj-admissible j (L⟨ R ⟩)
  → Rj-admissible j (L⟨ R ⟩)
reflj-adm→rj-adm {j} {R} ρ Γ a =
  mkAdmissibleRule λ { (d ∷ᵃ []ᵃ) →
    transportCtx {L = L⟨ R ⟩} {b = j a} (++-unit-r Γ)
      (Trans {U = Γ} {V₁ = []} {V₂ = []} d (AdmissibleRule.admit (ρ a) []ᵃ)) }

lj-adm→transj-adm
  : ∀ {j R}
  → Lj-admissible j (L⟨ R ⟩)
  → Transj-admissible j (L⟨ R ⟩)
lj-adm→transj-adm σ W U V a b =
  mkAdmissibleRule λ { (d₁ ∷ᵃ d₂ ∷ᵃ []ᵃ) →
    Trans d₁ (AdmissibleRule.admit (σ U V a b) (d₂ ∷ᵃ []ᵃ)) }

transj-adm→lj-adm
  : ∀ {j R}
  → Transj-admissible j (L⟨ R ⟩)
  → Lj-admissible j (L⟨ R ⟩)
transj-adm→lj-adm {j} τ U V a b =
  mkAdmissibleRule λ { (d ∷ᵃ []ᵃ) →
    AdmissibleRule.admit (τ (singleton (j a)) U V a b) (Refl ∷ᵃ d ∷ᵃ []ᵃ) }

jstab-adm→lj+-adm
  : ∀ {j R}
  → jstab-admissible j (L⟨ R ⟩)
  → Lj+-admissible j (L⟨ R ⟩)
jstab-adm→lj+-adm {j} σ U V a b =
  mkAdmissibleRule λ { (d ∷ᵃ []ᵃ) →
    Trans {U = singleton (j a)} {V₁ = U} {V₂ = V}
      (AdmissibleRule.admit (σ a) []ᵃ)
      d }

lj+-adm→jstab-adm
  : ∀ {j R}
  → Lj+-admissible j (L⟨ R ⟩)
  → jstab-admissible j (L⟨ R ⟩)
lj+-adm→jstab-adm σ a =
  mkAdmissibleRule λ _ → AdmissibleRule.admit (σ [] [] a a) (Refl ∷ᵃ []ᵃ)

-- Lemma 6 (derivable-form).
lemma6-derivable
  : ∀ {j R}
  → (Rj j (L⟨ R ⟩) ↔ Reflj j (L⟨ R ⟩))
  × (Lj j (L⟨ R ⟩) ↔ Transj j (L⟨ R ⟩))
  × (j-stab j (L⟨ R ⟩) ↔ Lj+ j (L⟨ R ⟩))
lemma6-derivable =
  intro rj→reflj reflj→rj
  , intro lj→transj transj→lj
  , intro jstab→lj+ lj+→jstab

-- Lemma 6 (admissible-form), kept explicit as a separate theorem.
lemma6-admissible
  : ∀ {j R}
  → (Rj-admissible j (L⟨ R ⟩) ↔ Reflj-admissible j (L⟨ R ⟩))
  × (Lj-admissible j (L⟨ R ⟩) ↔ Transj-admissible j (L⟨ R ⟩))
  × (jstab-admissible j (L⟨ R ⟩) ↔ Lj+-admissible j (L⟨ R ⟩))
lemma6-admissible =
  intro rj-adm→reflj-adm reflj-adm→rj-adm
  , intro lj-adm→transj-adm transj-adm→lj-adm
  , intro jstab-adm→lj+-adm lj+-adm→jstab-adm

lemma6
  : ∀ {j R}
  → (Rj j (L⟨ R ⟩) ↔ Reflj j (L⟨ R ⟩))
  × (Lj j (L⟨ R ⟩) ↔ Transj j (L⟨ R ⟩))
  × (j-stab j (L⟨ R ⟩) ↔ Lj+ j (L⟨ R ⟩))
lemma6 = lemma6-derivable

-- Lemma 8 package (items 1-4 in scope for this milestone).
lemma8
  : ∀ {j R}
  → (L⟨ R ⟩ ⊆ G⟨ j , R ⟩)
    × (L⟨ R ⟩ ⊆ M⟨ j , R ⟩)
    × BiNucleus j (G⟨ j , R ⟩)
    × BiNucleus j (M⟨ j , R ⟩)
    × ((∀ {R'} → R ⊆R R' → G⟨ j , R ⟩ ⊆ G⟨ j , R' ⟩)
      × (∀ {R'} → R ⊆R R' → M⟨ j , R ⟩ ⊆ M⟨ j , R' ⟩))
lemma8 =
  lift-base-into-G
  , lift-base-into-M
  , bi-on-G
  , bi-on-M
  , (lift-G , lift-M)

destab-mapSuccAll
  : ∀ {j R ps}
  → PremisesHold (M⟨ j , R ⟩) (map (mapSucc j) ps)
  → PremisesHold (M⟨ j , R ⟩) ps
destab-mapSuccAll {ps = []} []ᵃ = []ᵃ
destab-mapSuccAll {j} {R} {ps = p ∷ ps} (d ∷ᵃ ds) =
  destab-M {j = j} {R = R} d ∷ᵃ destab-mapSuccAll ds

-- Core internal step for Proposition 10: Gj(L) ⊆ Mj(L).
mutual

  g⊆m-all
    : ∀ {j R ps}
    → ExpansiveR j R
    → PremisesHold (G⟨ j , R ⟩) ps
    → PremisesHold (M⟨ j , R ⟩) ps
  g⊆m-all {ps = []} e []ᵃ = []ᵃ
  g⊆m-all {ps = p ∷ ps} e (d ∷ᵃ ds) = g⊆m e d ∷ᵃ g⊆m-all e ds

  g⊆m
    : ∀ {j R}
    → ExpansiveR j R
    → G⟨ j , R ⟩ ⊆ M⟨ j , R ⟩
  g⊆m e Refl = Refl
  g⊆m e (Trans d d₁) = Trans (g⊆m e d) (g⊆m e d₁)
  g⊆m {j} {R} e (ByRule (inl rr) ds) = ByRule (inl rr) (g⊆m-all e ds)
  g⊆m {j} {R} e (ByRule (inr (inl lj-instance)) ds) =
    jstab→lj+ {j = j} {R = MjRules j R}
      (λ a → jstab-in-M {j = j} {R = R} {a = a})
      (All-lookup-head (g⊆m-all e ds))
  g⊆m {j} {R} e (ByRule (inr (inr (rj-instance rr))) ds) =
    raise-M-from-expansiveR {j = j} {R = R} e
      (ByRule (inl rr) (destab-mapSuccAll (g⊆m-all e ds)))

kj⊆m
  : ∀ {j R}
  → Kj j (L⟨ R ⟩) ⊆ M⟨ j , R ⟩
kj⊆m {j} {R} {Γ} {a} d =
  destab-M {j = j} {R = R} (lift-base-into-M {j = j} {R = R} d)

-- Proposition 10: four inclusions proved internally.
proposition10
  : ∀ {j R}
  → ExpansiveR j R
  → (L⟨ R ⟩ ⊆ Kj j (L⟨ R ⟩))
    × (L⟨ R ⟩ ⊆ G⟨ j , R ⟩)
    × (G⟨ j , R ⟩ ⊆ M⟨ j , R ⟩)
    × (Kj j (L⟨ R ⟩) ⊆ M⟨ j , R ⟩)
proposition10 {j} {R} e with lemma8 {j} {R}
... | l⊆g , _ , _ , _ , _ =
  onBase-ExpansiveR e , l⊆g , g⊆m e , kj⊆m

-- Theorem 11 (Conservation), clauses (1)-(4).
theorem11
  : ∀ {j R R'}
  → ExpansiveR j R
  → (L⟨ R ∪R R' ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩))
    × ((Kj j (L⟨ R ∪R R' ⟩) ⊆ L⟨ R ∪R R' ⟩) ↔ (M⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩))
    × ((Kj j (L⟨ R ∪R R' ⟩) ⊆ M⟨ j , R ⟩) ↔ (L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩))
    × ((M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩)) ↔ (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩))
theorem11 {j} {R} {R'} e =
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
  l'⊆k = lift-ExpansiveR e (λ rr → inl rr)

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

  mutual

    m→gj-all
      : ∀ {ps}
      → PremisesHold M ps
      → PremisesHold G (map (mapSucc j) ps)
    m→gj-all {ps = []} []ᵃ = []ᵃ
    m→gj-all {ps = p ∷ ps} (d ∷ᵃ ds) = m→gj d ∷ᵃ m→gj-all ds

    m→gj
      : ∀ {Γ a}
      → M Γ a
      → G Γ (j a)
    m→gj Refl = lift-ExpansiveR e (λ rr → inl rr) Refl
    m→gj (Trans d d₁) = Trans (m→gj d) (embed-Lj (m→gj d₁))
    m→gj (ByRule (inl rr) ds) = ByRule (inr (inr (rj-instance rr))) (m→gj-all ds)
    m→gj (ByRule (inr jstab-instance) ds) = Refl

  c4-from : G ⊆ L' → M ⊆ K'
  c4-from g⊆l' d = g⊆l' (m→gj d)

-- ============================================================================
-- CSL 2026 layer (Theorem 6-oriented API)
-- ============================================================================

R'DerivableInMax : ∀ {j : S → S} {R R' : RuleSet} → Type ℓ
R'DerivableInMax {j} {R} {R'} = ∀ {r} → R' r → DerivableRule r (Max⟨ j , R ⟩)

JHomogeneous : ∀ {j k : S → S} {R : RuleSet} → Type ℓ
JHomogeneous {j} {k} {R} =
  Nucleus k (Max⟨ j , R ⟩)
  × StableNucleus j (Lift1 k (L⟨ R ⟩))

A2026 : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
A2026 {j} {k} {R} {R'} = Max⟨ j , R ⟩ ⊆ Lift1 k (L⟨ R ∪R R' ⟩)

B2026 : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
B2026 {j} {k} {R} {R'} =
  ∀ {r} → (R ∪R R') r → AdmissibleRule r (Lift1 k (L⟨ R ∪R R' ⟩))

C2026 : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
C2026 {j} {k} {R} {R'} = Kol1⟨ k , R ⟩ ⊆ L⟨ R ∪R R' ⟩

theorem6-statement : ∀ {j k : S → S} {R R' : RuleSet} → Type ℓ
theorem6-statement {j} {k} {R} {R'} =
  (A2026 {j} {k} {R} {R'} ↔ B2026 {j} {k} {R} {R'})
  × (B2026 {j} {k} {R} {R'} ↔ C2026 {j} {k} {R} {R'})

premises-⊆
  : ∀ {L L' : Entailment} {ps : List Seq}
  → L ⊆ L'
  → PremisesHold L ps
  → PremisesHold L' ps
premises-⊆ {ps = []} i []ᵃ = []ᵃ
premises-⊆ {ps = p ∷ ps} i (d ∷ᵃ ds) = i d ∷ᵃ premises-⊆ i ds

lift1-all→
  : ∀ {k : S → S} {L : Entailment} {ps : List Seq}
  → PremisesHold (Lift1 k L) ps
  → PremisesHold L (map (mapBoth k) ps)
lift1-all→ {ps = []} []ᵃ = []ᵃ
lift1-all→ {k} {L} {ps = p ∷ ps} (d ∷ᵃ ds) = d ∷ᵃ lift1-all→ {k} {L} {ps} ds

lift1-all←
  : ∀ {k : S → S} {L : Entailment} {ps : List Seq}
  → PremisesHold L (map (mapBoth k) ps)
  → PremisesHold (Lift1 k L) ps
lift1-all← {ps = []} []ᵃ = []ᵃ
lift1-all← {k} {L} {ps = p ∷ ps} (d ∷ᵃ ds) = d ∷ᵃ lift1-all← {k} {L} {ps} ds

lift1-adm→mapBoth-adm
  : ∀ {k : S → S} {L : Entailment} {r : Rule}
  → AdmissibleRule r (Lift1 k L)
  → AdmissibleRule (mapBothRule k r) L
lift1-adm→mapBoth-adm {k} {L} {r} a =
  mkAdmissibleRule λ ds → AdmissibleRule.admit a (lift1-all← {k} {L} {premises r} ds)

mapBoth-adm→lift1-adm
  : ∀ {k : S → S} {L : Entailment} {r : Rule}
  → AdmissibleRule (mapBothRule k r) L
  → AdmissibleRule r (Lift1 k L)
mapBoth-adm→lift1-adm {k} {L} {r} a =
  mkAdmissibleRule λ ds → AdmissibleRule.admit a (lift1-all→ {k} {L} {premises r} ds)

lemma2-2026
  : ∀ {k : S → S} {R : RuleSet} {r : Rule}
  → R r
  → AdmissibleRule r (Lift1 k (Kol1⟨ k , R ⟩))
lemma2-2026 {k} {R} {r} rr =
  mapBoth-adm→lift1-adm (derivable→admissible (embed-Rk1 {k} {R} {r} rr))

max-in-R→R∪R'
  : ∀ {j : S → S} {R R' : RuleSet}
  → Max⟨ j , R ⟩ ⊆ Max⟨ j , R ∪R R' ⟩
max-in-R→R∪R' {j} {R} {R'} = lift-⊆R embed
  where
  embed : MaxRules j R ⊆R MaxRules j (R ∪R R')
  embed (inl rr) = inl (inl rr)
  embed (inr rest) = inr rest

jstab-in-Max
  : ∀ {j : S → S} {R : RuleSet} {a : S}
  → Max⟨ j , R ⟩ (singleton (j a)) a
jstab-in-Max {j} {R} {a} = embed-Lj+ {j} {R} {U = []} {V = []} {a = a} {b = a} Refl

destab-Max
  : ∀ {j : S → S} {R : RuleSet} {Γ : Ctx} {a : S}
  → Max⟨ j , R ⟩ Γ (j a)
  → Max⟨ j , R ⟩ Γ a
destab-Max {j} {R} {Γ} {a} d =
  transportCtx {L = Max⟨ j , R ⟩} {b = a} (++-unit-r Γ)
    (Trans {U = Γ} {V₁ = []} {V₂ = []} {a = j a} {b = a} d jstab-in-Max)

proposition5-2026
  : ∀ {j k : S → S} {R R' : RuleSet}
  → R'DerivableInMax {j} {R} {R'}
  → JHomogeneous {j} {k} {R}
  → (Max⟨ j , R ∪R R' ⟩ ⊆ Max⟨ j , R ⟩)
  → (Max⟨ j , R ⟩ ⊆ Max⟨ j , R ∪R R' ⟩)
  → JHomogeneous {j} {k} {R ∪R R'}
  → (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → (Kj j (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → (Max⟨ j , R ∪R R' ⟩ ⊆ Max⟨ j , R ⟩)
    × (Max⟨ j , R ⟩ ⊆ Max⟨ j , R ∪R R' ⟩)
    × JHomogeneous {j} {k} {R ∪R R'}
    × (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
    × (Kj j (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
proposition5-2026 {j} {k} {R} {R'} ρ hom max'⊆max max⊆max' hom' lift⊆max kj⊆max =
  max'⊆max
  , max⊆max'
  , hom'
  , lift⊆max
  , kj⊆max

transport-admissible
  : ∀ {r : Rule} {L L' : Entailment}
  → L ⊆ L'
  → L' ⊆ L
  → AdmissibleRule r L
  → AdmissibleRule r L'
transport-admissible to from a =
  mkAdmissibleRule λ ds → to (AdmissibleRule.admit a (premises-⊆ from ds))

a⇒b-2026
  : ∀ {j k : S → S} {R R' : RuleSet}
  → R'DerivableInMax {j} {R} {R'}
  → (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → A2026 {j} {k} {R} {R'}
  → B2026 {j} {k} {R} {R'}
a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max a {r} (inl rr0) =
  transport-admissible a lift⊆max
    (derivable→admissible (rule-is-derivable (inl rr0)))
a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max a {r} (inr rr') =
  transport-admissible a lift⊆max
    (derivable→admissible (ρ rr'))

b⇒a-2026
  : ∀ {j k : S → S} {R R' : RuleSet}
  → JHomogeneous {j} {k} {R ∪R R'}
  → (B2026 {j} {k} {R} {R'} → A2026 {j} {k} {R} {R'})
  → B2026 {j} {k} {R} {R'}
  → A2026 {j} {k} {R} {R'}
b⇒a-2026 hom b⇒a b = b⇒a b

theorem6
  : ∀ {j k : S → S} {R R' : RuleSet}
  → R'DerivableInMax {j} {R} {R'}
  → JHomogeneous {j} {k} {R ∪R R'}
  → (Lift1 k (L⟨ R ∪R R' ⟩) ⊆ Max⟨ j , R ⟩)
  → (B2026 {j} {k} {R} {R'} → A2026 {j} {k} {R} {R'})
  → (A2026 {j} {k} {R} {R'} → B2026 {j} {k} {R} {R'} → C2026 {j} {k} {R} {R'})
  → (C2026 {j} {k} {R} {R'} → A2026 {j} {k} {R} {R'})
  → theorem6-statement {j} {k} {R} {R'}
theorem6 {j} {k} {R} {R'} ρ hom' lift⊆max b⇒a ab⇒c c⇒a =
  intro (a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max) (b⇒a-2026 {j} {k} {R} {R'} hom' b⇒a)
  ,
  intro
    (λ b → ab⇒c (b⇒a-2026 {j} {k} {R} {R'} hom' b⇒a b) b)
    (λ c → a⇒b-2026 {j} {k} {R} {R'} ρ lift⊆max (c⇒a c))

theorem6-k=j-compatible
  : ∀ {j : S → S} {R R' : RuleSet}
  → ExpansiveR j R
  → (M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩))
    ↔ (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩)
theorem6-k=j-compatible e = snd (snd (snd (theorem11 e)))
