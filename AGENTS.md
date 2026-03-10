# AGENTS.md — Codex Repo Guide for Cubical Agda

This file provides persistent repo-specific context for Codex when working on this Cubical Agda project. It is the Codex-side companion to `CLAUDE.md` (which governs Claude-side orchestration).

---

## Agda Conventions

### Import rules

- Use ONLY `Cubical.*` imports from the cubical library.
- Do NOT use agda-stdlib or 1Lab imports.
- Never import `Cubical.Everything` — it loads the entire library and destroys typechecking performance.
- Preferred entry points:
  - `open import Cubical.Core.Everything` — just primitives (I, PathP, Glue, transport, hcomp)
  - `open import Cubical.Foundations.Prelude` — default for most work (paths, funExt, transport, subst, J, h-levels)
  - Add more specific `Cubical.*` imports as needed
- Use `Cubical.Foundations.Everything` only if the module genuinely needs a broad slice of foundations.
- Prefer `using` clauses when only 1–3 names are used from a module.

### Style

- Lemma names: `camelCase`
- Module names: match directory structure
- Prefer named helper lemmas over giant inline proof terms
- Comment interval variables (`i`, `j`) when the geometry is not obvious
- Prefer path-based proofs unless the module explicitly declares Id-based style

### Typecheck discipline

- Run `agda FILE.agda` after every lemma.
- Do not continue to the next lemma if typechecking fails.
- Do not leave unsolved holes in completed lemmas.
- If typechecking hangs for >60 seconds, the proof term is too complex — break it into helpers.

---

## Import Reference (Condensed)

This is the canonical mapping. If in doubt, search the library source rather than guessing.

### Paths and basic reasoning

| I need... | Import |
|-----------|--------|
| refl, sym, cong, cong₂ | `Cubical.Foundations.Prelude` |
| `_∙_` (path composition) | `Cubical.Foundations.Prelude` |
| funExt, funExt⁻ | `Cubical.Foundations.Prelude` |
| transport, subst, transportRefl | `Cubical.Foundations.Prelude` |
| J, JRefl | `Cubical.Foundations.Prelude` |
| toPathP, fromPathP | `Cubical.Foundations.Prelude` |
| Equational reasoning `_≡⟨_⟩_`, `_∎` | `Cubical.Foundations.Prelude` |
| Path associativity, unit, inverse laws | `Cubical.Foundations.GroupoidLaws` |
| PathP lemmas, square fillers | `Cubical.Foundations.Path` |
| Transport lemmas, pathToIso | `Cubical.Foundations.Transport` |

### Equivalences and isomorphisms

| I need... | Import |
|-----------|--------|
| `_≃_`, equivFun, idEquiv | `Cubical.Core.Glue` (re-exported by Core.Everything) |
| Iso record, isoToEquiv, isoToPath | `Cubical.Foundations.Isomorphism` |
| isPropIsEquiv, `_∙ₑ_`, invEquiv | `Cubical.Foundations.Equiv` |
| funExt is an equivalence | `Cubical.Functions.FunExtEquiv` |

### Univalence

| I need... | Import |
|-----------|--------|
| ua, uaβ, pathToEquiv, univalence | `Cubical.Foundations.Univalence` |
| EquivJ, elimEquiv, elimIso | `Cubical.Foundations.Univalence` |
| hPropExt | `Cubical.Foundations.Univalence` |

### h-Levels

| I need... | Import |
|-----------|--------|
| isContr, isProp, isSet, isGroupoid | `Cubical.Foundations.Prelude` (predicates) |
| isOfHLevel, isOfHLevelΣ, isOfHLevelΠ | `Cubical.Foundations.HLevels` |
| isProp→isSet, Hedberg | `Cubical.Foundations.HLevels` |

### Higher inductive types

| I need... | Import |
|-----------|--------|
| ∥ A ∥₁ (propositional truncation) | `Cubical.HITs.PropositionalTruncation` |
| ∥ A ∥₂ (set truncation) | `Cubical.HITs.SetTruncation` |
| A / R (set quotients) | `Cubical.HITs.SetQuotients` |
| S¹, base, loop | `Cubical.HITs.S1` |
| Pushouts | `Cubical.HITs.Pushout` |
| Suspension | `Cubical.HITs.Susp` |

### Data types

| I need... | Import |
|-----------|--------|
| ℕ | `Cubical.Data.Nat` |
| ℤ | `Cubical.Data.Int` |
| Bool | `Cubical.Data.Bool` |
| ⊥, ⊤ | `Cubical.Data.Empty`, `Cubical.Data.Unit` |
| Σ-types | `Cubical.Data.Sigma` |
| A ⊎ B | `Cubical.Data.Sum` |
| List | `Cubical.Data.List` |
| Fin | `Cubical.Data.Fin` |

### Algebra

| I need... | Import |
|-----------|--------|
| Monoid | `Cubical.Algebra.Monoid` |
| Group, GroupHom | `Cubical.Algebra.Group.Base` |
| Ring, CommRing | `Cubical.Algebra.Ring`, `Cubical.Algebra.CommRing` |
| Category | `Cubical.Categories.Category.Base` |

### Other

| I need... | Import |
|-----------|--------|
| Decidability | `Cubical.Relation.Nullary` |
| SIP (Structure Identity Principle) | `Cubical.Foundations.SIP` |
| Pointed types | `Cubical.Foundations.Pointed` |

### Known corrections

- `funExt` is in `Cubical.Foundations.Prelude`, **not** `Cubical.Foundations.Function`.
- K / axiom K is **not available** under `--cubical`. Use J (path induction) instead.

---

## Common Cubical Agda Error Patterns

### "X != Y of type Z"
Unification failure. Check: wrong universe level? Missing transport or subst? Forgot funExt or pathToFun?

### "Cannot instantiate the metavariable _ to solution X"
Agda can't infer an implicit. Provide it explicitly: `f {A = MyType}` or add a type annotation.

### "Termination checking failed"
Recursive call isn't structurally smaller. Check pattern matching argument. For HITs, ensure path constructors reduce. Consider `Cubical.Induction.WellFounded`.

### "I'm not sure if there should be a case for the constructor hcomp"
Need to handle the `hcomp` case when pattern matching on HITs. Use `elimProp` or `elimSet` if the target is a proposition or set. Add an explicit `hcomp` case if the target has higher structure.

### "Primcubicalcomp: __IMPOSSIBLE__"
Internal cubical failure. Usually means transp or hcomp applied to something non-fibrant. Restructure to avoid direct hcomp; use library combinators instead.

### Timeout / hang (>60 seconds)
Proof term too large for normalization. Break into smaller helpers with explicit type signatures. Use `abstract` to block unnecessary normalization. Add more type annotations.

---

## Stuck Packet Format

If you cannot fill a hole, report exactly this:

```
## Stuck Report

### Goal type
[exact type Agda expects in the hole]

### Context
[bindings currently in scope]

### Attempted
[which cubical primitives were tried: funExt, transport, cong, J, hcomp, glue, ...]

### Normalization
[any C-c C-n results on subexpressions, or "not attempted"]

### Blocked on
[what specifically prevents progress]
```

Do not continue past a stuck hole. Report the packet and stop.

---

## Cubical Proof Patterns Cookbook

When you encounter a goal, match its shape to a known pattern before attempting a custom proof.

### Path goals

| Goal shape | Try first | Then try |
|------------|-----------|----------|
| `Path A x y` (concrete x, y) | Direct `λ i → ...` construction | `cong f p` if x and y are images of f |
| `f ≡ g` (function equality) | `funExt (λ x → ...)` | — |
| `PathP (λ i → A i) x y` | `toPathP (...)` | Direct `λ i → ...` with transport |
| `Square ...` | Library fillers from `Cubical.Foundations.Path` | Direct `λ i j → ...` |

### Equivalence and identity goals

| Goal shape | Try first | Then try |
|------------|-----------|----------|
| `A ≃ B` | Build an `Iso` first, then `isoToEquiv` | Direct `equivFun` + `equivProof` |
| `A ≡ B` (type equality) | Build `A ≃ B`, then `ua` | Direct `isoToPath` |
| `isEquiv f` | Build `Iso` with f as `fun`, then `isoToEquiv .snd` | — |
| `transport p x ≡ y` | `transportRefl` if p = refl | `substCommSlice` or manual |

### h-Level goals

| Goal shape | Try first | Then try |
|------------|-----------|----------|
| `isProp X` | Direct proof `λ x y → ...` | Derive from `isContr X` |
| `isSet X` | `isProp→isSet` if you have isProp | `Hedberg` if X has decidable equality |
| `isOfHLevel n (Σ A B)` | `isOfHLevelΣ` | — |
| `isOfHLevel n (Π A B)` | `isOfHLevelΠ` | — |
| `isOfHLevel n (Path A x y)` | `isOfHLevelPath` | — |

### HIT elimination goals

| Goal shape | Try first | Then try |
|------------|-----------|----------|
| `∥ A ∥₁ → B` (B is a prop) | `rec isPropB f` | `elim` if you need the full eliminator |
| `∥ A ∥₂ → B` (B is a set) | `rec isSetB f` | `elim` for dependent case |
| `A / R → B` (B is a set) | `rec isSetB f feq` | — |
| HIT → set/prop | Use `elimSet` / `elimProp` | Avoids needing explicit hcomp case |

### Transport and composition

| Goal shape | Try first | Then try |
|------------|-----------|----------|
| `transport refl x ≡ x` | `transportRefl x` | — |
| `subst B p x ≡ y` | Unfold subst as transport, simplify | `substCommSlice` |
| Need to fill a cube | `hfill` for partial filling | Direct `hcomp` with explicit system |

### General strategies

- If a direct proof is getting complicated, check the library — the lemma likely exists.
- Before writing a new lemma, `grep` the cubical library source for the type signature pattern.
- If normalization is slow, add type annotations and break into named helpers.
- If a `hcomp` case is required, switch to `elimProp` / `elimSet` if possible.

---

## Commands

```bash
agda FILE.agda                    # typecheck single file
agda src/Everything.agda          # typecheck whole project
```
