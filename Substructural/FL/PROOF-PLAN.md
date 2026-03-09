# Proof Plan: theorem19 (Theorem thm-FL)

## Goal
Prove `theorem19` matching the paper's Theorem thm-FL (MAIN.tex:626–643).

```agda
theorem19-proof
  : ∀ {j R}
  → FLRules ⊆R R
  → theorem19 j (Deriv R)
```

## Allowed Imports
- Cubical.Core.Primitives (for Type)
- Cubical.Data.List.Properties (for ++-unit-r)
- Substructural.Prelude
- Substructural.FL.{Formula, Rules, Basic, Shifts}
- Substructural.Core.{Judgement, Rules, Derivation, Nucleus, Extensions, Conservation}

## Conventions
- Style: Path-based
- Universe: polymorphic (ℓ)
- Naming: camelCase, lemma prefixes match paper numbering

## Lemma Decomposition

| # | Name | Type | Strategy | Status |
|---|------|------|----------|--------|
| 1 | `foldCtx` | `Formula → Ctx → Formula` | Left-assoc: `foldCtx a [] = a`, `foldCtx a (v∷V) = foldCtx (a·v) V` | ☐ |
| 2 | `foldL-·` | `Deriv R (plug₁ U a V) c → Deriv R (suffix U (foldCtx a V)) c` | Induction on V, iterated L· | ☐ |
| 3 | `foldR-shift·` | `(a : Formula)(V : Ctx) → Deriv R (j a ∷ V) (j (foldCtx a V))` | Induction on V, iterated R· + Rj + shift· + Trans | ☐ |
| 4 | `ljleft+shift·→lj` | `FLRules ⊆R R → Rj j (Deriv R) → Ljleft j (Deriv R) → Shift· j (Deriv R) → Lj j (Deriv R)` | V=[] by Ljleft; V=v∷V' by #2 + Ljleft + #3 + Trans | ☐ |
| 5 | `ljright+shift·→lj` | Same but `Ljright` | Symmetric to #4 (fold from right of U) | ☐ |
| 6 | `shiftCoreInG-FL` | `ShiftCoreDerivableInG j FLRules` | 4 cases, same as `shiftCoreInG-FLe` with `inl` injection | ☐ |
| 7 | `shift·-in-ext` | `Shift· j (L⟨ ShiftCoreExt j FLRules ⟩)` | From `shift·-instance` axiom | ☐ |
| 8 | `lj-ext-FL` | `nucleus sum → Expansive → Lj j (L⟨ShiftCoreExt j FLRules⟩)` | Case split: Bi → lift; Left → lift Ljleft + #4 + #7; Right → lift Ljright + #5 + #7 | ☐ |
| 9 | `survive-L⊸›-ext-FL` | `L⊸j-local × L›j-local` in ShiftCoreExt | `lemma16-5-proof inl (mkBiNucleus rj lj)` with lj from #8 | ☐ |
| 10 | `surv-FL` | `∀ {r} → FLRules r → SurvivesAfter j r (ShiftCoreExt j FLRules)` | 14 cases following `surv-FLe` pattern | ☐ |
| 11 | `lemma17-FL` | `G⟨j,FLRules⟩ ⊆ L⟨ShiftCoreExt j FLRules⟩ × reverse` | `lemma17-proof (#8) (#10) (#6)` | ☐ |
| 12 | `cond2→cond1` | `G ⊆ Deriv R → Cond1` | Fwd: `m→gj` + G⊆L; Bwd: `L⊆M` + `destab-M` | ☐ |
| 13 | `cond1→cond2` | `Cond1 → G ⊆ Deriv R` | Induction on G-derivations using `FLRules ⊆R R`, `m⊆k`, `jj→j` | ☐ |
| 14 | `cond2↔cond3` | `Cond2 ↔ Cond3` for `Deriv R` | Fwd: extract shifts from G; Bwd: #11 + embed ShiftCoreExt | ☐ |
| 15 | `theorem19-proof` | `FLRules ⊆R R → theorem19 j (Deriv R)` | Combine #12–14, case split on nucleus variant | ☐ |

## Dependencies
```
#1 ← #2, #3
#2, #3 ← #4, #5
#4, #5 ← #8
#6, #7 ← #8
#8 ← #9 ← #10 ← #11
#11 ← #14
#12, #13 ← #15
#14 ← #15
```

## Item (4) proof sketch (MAIN.tex:858–884)

Given `U, a, V ⊢ j(b)`, derive `U, j(a), V ⊢ j(b)`:

**V = []**: direct by Ljleft.

**V = v∷V'**:
1. `foldL-·`: `U, a, V ⊢ j(b)` → `U, foldCtx(a,V) ⊢ j(b)` via iterated L·
2. Ljleft: `U, j(foldCtx(a,V)) ⊢ j(b)`
3. `foldR-shift·`: `j(a), V ⊢ j(foldCtx(a,V))` via iterated (R· + Rj + shift·)
4. Trans #3 into #2: `U, j(a), V ⊢ j(b)` ✓

Left-assoc fold: `foldCtx a [v₁,...,vₙ] = ((...(a·v₁)·v₂)·...)·vₙ`.

## Nucleus variant handling

The `theorem19` type takes `RightNucleus j FL ⊎ (LeftNucleus j FL ⊎ BiNucleus j FL)`.

For `lj-ext-FL` (#8), we need `Lj j (L⟨ShiftCoreExt j FLRules⟩)`:
- **BiNucleus**: has full Lj on FL. Need BiProgressiveR to lift to ShiftCoreExt. If not available, use item (4): BiNucleus gives both Ljleft and Ljright, use either + shift· in ShiftCoreExt.
- **LeftNucleus**: has Ljleft on FL. Lift Ljleft to ShiftCoreExt (by induction: FL rule cases identical, ShiftCoreRules cases use Rj). Then upgrade via #4 + shift·-in-ext.
- **RightNucleus**: symmetric via Ljright + #5.

**Key**: Lifting `Ljleft j FL` to `Ljleft j (L⟨ShiftCoreExt j FLRules⟩)` requires proving Ljleft is preserved under rule extension. This is NOT automatic — need induction on derivations in ShiftCoreExt and case analysis on ShiftCoreRules (4 new cases). Each ShiftCoreRule has no premises and a singleton antecedent, so the Ljleft case is: from `U, singleton(x) ⊢ j(b)` where x is a shift formula, derive `U, j(singleton(x)) ⊢ j(b)`. This uses Rj (expansiveness) + Trans.

## Existing code to reuse
- `lemma17-proof` (Shifts.agda:535)
- `lemma16-5-proof` (Shifts.agda:316) — L⊸/L› survival from BiNucleus
- `m→gj` (Conservation.agda:601) — M → G(j·)
- `destab-M` (Extensions.agda:233) — M Γ (j a) → M Γ a
- `surv-FLe` (Lemma17.agda:90) — template for surv-FL
- `shiftCoreInG-FLe` (Lemma17.agda:16) — template for shiftCoreInG-FL

## Rejected Approaches
(none yet)

## Open Questions
1. `cond1→cond2` (#13): reuse `c4-to` from Conservation.agda (works for `L⟨R ∪R R'⟩`) or write direct induction for `Deriv R`?
2. Lifting Ljleft to ShiftCoreExt: can we generalize `LeftProgressiveR` or must we do the induction inline?
