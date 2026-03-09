# Proof Plan: Batch 7 — Glivenko-Cond + corollary22 assembly

## Status

Batches 6/6b (Ono + Odintsov equivalences) are DONE and typechecked.
Remaining: Batch 7 — `gli⊆int`, `int⊆cla`, `glivenko-cond-proof`, `corollary22-proof`.

## Available helpers (already typechecked in Glivenko.agda)

```
ono-cond2→cond1  : Deriv R ⊆ InFLe → Ono-Cond2 (Deriv R) → Ono-Cond1 (Deriv R)
ono-cond1→cond2  : FLeRules ⊆R R → Ono-Cond1 (Deriv R) → Ono-Cond2 (Deriv R)
ono-cond2→cond3  : Ono-Cond2 (Deriv R) → Ono-Cond3 (Deriv R)
ono-cond3→cond2  : FLeRules ⊆R R → Ono-Cond3 (Deriv R) → Ono-Cond2 (Deriv R)

odintsov-cond2→cond1  : Deriv R ⊆ Cla → Odintsov-Cond2 (Deriv R) → Odintsov-Cond1 (Deriv R)
odintsov-cond1→cond2  : MinRules ⊆R R → Odintsov-Cond1 (Deriv R) → Odintsov-Cond2 (Deriv R)
odintsov-cond2→cond3  : Odintsov-Cond2 (Deriv R) → Odintsov-Cond3 (Deriv R)
odintsov-cond3→cond2  : MinRules ⊆R R → Odintsov-Cond3 (Deriv R) → Odintsov-Cond2 (Deriv R)
shift›-from-shift⊸    : FLeRules ⊆R R → Shift⊸ nn (Deriv R) → Shift› nn (Deriv R)
```

## File: Substructural/FL/Glivenko.agda

All new code goes AFTER line 672 (end of `odintsov-cond3→cond2`).

## Imports already present

```
open import Substructural.Core.Conservation Formula
  using (transportCtx; g⊆m; m→gj; jstab→lj+; destab-mapSuccAll)
```

Extensions.agda imported fully (so `destab-M`, `jstab-in-M`, `lift-base-into-M`,
`raise-M-from-expansive`, `embed-Lj` etc. are in scope).

## Key definitions

- `IntRules = MinRules ∪R L0Rules` (Rules.agda:117-118)
- `Int = L⟨ IntRules ⟩ = Deriv IntRules` (Rules.agda:125)
- `Cla = M⟨ nn , MinRules ⟩` (Glivenko.agda:38)
- `Gli = G⟨ nn , MinRules ⟩` (Glivenko.agda:41)
- `Glivenko-Cond = ∀ {Γ a} → Cla Γ a ↔ Int Γ (¬¬ a)` (Glivenko.agda:384)

- `L0Rules` data type (Rules.agda:109-115):
  ```agda
  data L0Rules : RuleSet where
    l0-instance : ∀ {U V c}
      → L0Rules (mkRule ((plug₁ U `0 V ▷ c) ∷ []) (U ++ V ▷ c))
  ```
  One premise: `plug₁ U `0 V ⊢ c` = `U ++ (`0 ∷ V) ⊢ c`. Conclusion: `U ++ V ⊢ c`.

- `M⟨j,R⟩` rules: `inl rr` (base R rule), `inr jstab-instance` (j-stability: `[j a] ⊢ a`).

## Lemma table

| # | Name | Type | Strategy | Status |
|---|------|------|----------|--------|
| 1 | `gli⊆int` | `Gli ⊆ Int` | Instantiate `odintsov-cond1→cond2` with `R = IntRules`. Need `Odintsov-Cond1 (Int)`, which is `∀ {Γ a} → Cla Γ a ↔ Int Γ (nn a)`. This IS Glivenko-Cond. **Circular with glivenko-cond-proof.** See alternative below. | ☐ |
| 2 | `int⊆cla` | `Int ⊆ Cla` | Mutual recursion on `Deriv IntRules Γ a` → `M⟨nn,Min⟩ Γ a`. See detailed proof below. | ☐ |
| 3 | `glivenko-cond-proof` | `Glivenko-Cond` | `→` and `←` both need gli⊆int and int⊆cla. See detailed proof below. | ☐ |
| 4 | `corollary22-proof` | `corollary22` | Assemble: `(ono-part , odintsov-part , glivenko-cond-proof)`. | ☐ |

## Refined strategy (avoiding circularity)

The `gli⊆int` approach via `odintsov-cond1→cond2` is circular. Instead:

### gli⊆int: direct proof

`Gli ⊆ Int` = `G⟨nn,Min⟩ ⊆ Deriv IntRules`.

Mutual recursion on G derivations, same pattern as `odintsov-cond1→cond2`:
```agda
gli⊆int : Gli ⊆ Int
```

- `Refl → Refl`
- `Trans d₁ d₂ → Trans (gli⊆int d₁) (gli⊆int d₂)`
- `ByRule (inl rr) ds → ByRule (iMin rr) (gli⊆int-all ds)` where `iMin : MinRules ⊆R IntRules = inj₁`
- `ByRule (inr (inl (lj-instance {b = b}))) ds →`
  Need: `Deriv IntRules Γ (nn b)` given we can get `Deriv IntRules Γ (nn (nn b))` from `gli⊆int`.
  Build `jj→j b : Int [nn(nn b)] (nn b)` using the Odintsov Cond1 approach:
  - Derive `M⟨nn,Min⟩ [nn(nn b)] b` via `jstab→lj+ jstab-in-M` applied to jstab-in-M
  - Then `to (glivenko-cond {Γ = [nn(nn b)]} {a = b})` to get `Int [nn(nn b)] (nn b)`
  **STILL CIRCULAR** — glivenko-cond uses gli⊆int.

### True non-circular approach

Build `jj→j` directly in Int without going through Glivenko-Cond:

```agda
jj→j : ∀ b → Int (singleton (nn (nn b))) (nn b)
```

Proof: `nn(nn b) = ((b⊸0)⊸0)⊸0)⊸0`. Need `[(((b⊸0)⊸0)⊸0)⊸0] ⊢ (b⊸0)⊸0` in Int.

Steps (all in `Deriv IntRules`, which has full FL + Comm + Mono + Contr + L0):
1. `Refl : [nn(nn b)] ⊢ nn(nn b)` = `[((b⊸0)⊸0)⊸0)⊸0] ⊢ ((b⊸0)⊸0)⊸0)⊸0`
2. By `mp⊸-in`: `(b⊸0)⊸0, ((b⊸0)⊸0)⊸0 ⊢ 0`
3. By Comm: `((b⊸0)⊸0)⊸0, (b⊸0)⊸0 ⊢ 0`
4. By R⊸: `((b⊸0)⊸0)⊸0 ⊢ (b⊸0)⊸0`  -- Wait, R⊸ gives `Γ ⊢ a⊸b` from `a,Γ ⊢ b`. Here a=(b⊸0), b=0, Γ=[(((b⊸0)⊸0)⊸0)]. So we'd get `[((b⊸0)⊸0)⊸0] ⊢ (b⊸0)⊸0`... but that's `[nn(nn b)⊸0] ⊢ nn b`, not `[nn(nn b)] ⊢ nn b`.

Hmm, that doesn't work directly. Actually:

We want `[nn(nn b)] ⊢ nn b`. Expand: `[(nn b ⊸ 0) ⊸ 0] ⊢ nn b`.
The outer structure of `nn(nn b)` is `X ⊸ 0` where `X = nn b ⊸ 0`.
By R⊸: to get `[nn(nn b)] ⊢ nn b = (b⊸0)⊸0`, need `(b⊸0), [nn(nn b)] ⊢ 0`.
By mp⊸ on nn(nn b): need `nn b ⊸ 0` and `nn(nn b)`. We have nn(nn b) in context.
So: `(b⊸0), [nn(nn b)] ⊢ 0` via:
  - Build `nn b = (b⊸0)⊸0` from `(b⊸0)` and `0`... hmm.

Actually simpler:
- `Rnn-R : Γ ⊢ a → Γ ⊢ nn a` (from DoubleNegation.agda, needs FLeRules ⊆R R)
- `Refl : [nn b] ⊢ nn b`
- So `Rnn-R Refl : [nn b] ⊢ nn(nn b)`
- Trans + identity argument... no.

The simplest `jj→j` in Int:
Since Int has Comm (from MinRules), and all FL rules:

```
[nn(nn b)] ⊢ nn b
```

Step 1: R⊸ introduction — to prove `[nn(nn b)] ⊢ (b⊸0)⊸0`, suffices to prove
  `(b⊸0), nn(nn b) ⊢ 0`.
Step 2: In context `(b⊸0), nn(nn b)`:
  - `(b⊸0) : b⊸0` and `nn(nn b) = ((b⊸0)⊸0)⊸0`
  - By `Rnn-R` on identity `(b⊸0) ⊢ b⊸0`, we get `(b⊸0) ⊢ nn(b⊸0) = ((b⊸0)⊸0)⊸0`... no, Rnn-R gives `Γ ⊢ a → Γ ⊢ nn a`, so `[b⊸0] ⊢ nn(b⊸0)`.
  But nn(b⊸0) = ((b⊸0)⊸0)⊸0 which is NOT the same as nn(nn b) = ((b⊸0)⊸0)⊸0.
  Actually nn(b⊸0) = (((b⊸0)⊸0)⊸0) and nn(nn b) = nn((b⊸0)⊸0) = (((b⊸0)⊸0)⊸0)⊸0.
  Hmm, nn(b⊸0) = ((b⊸0) ⊸ 0) ⊸ 0 and nn(nn b) = (((b⊸0)⊸0) ⊸ 0) ⊸ 0. These are different.

OK let me think more carefully.

nn b = (b ⊸ 0) ⊸ 0
nn(nn b) = (nn b ⊸ 0) ⊸ 0 = (((b ⊸ 0) ⊸ 0) ⊸ 0) ⊸ 0

We want: `[nn(nn b)] ⊢ nn b` in Int.

Using R⊸: to prove `[X⊸0⊸0] ⊢ Y⊸0⊸0` where X = nn b ⊸ 0 and Y = b ⊸ 0:

Suffices to prove `(b⊸0), [nn(nn b)] ⊢ 0`:
- From (b⊸0), build nn b:
  - Rnn-R on `Refl : [b⊸0] ⊢ b⊸0` gives `[b⊸0] ⊢ nn(b⊸0)`.
  But nn(b⊸0) ≠ nn b. So this doesn't directly help.

Alternative: use L⊸ on nn(nn b) = (nn b ⊸ 0) ⊸ 0.
L⊸ decomposes `nn(nn b) = (nn b ⊸ 0) ⊸ 0` in the antecedent.
L⊸ rule: from `U ⊢ a` and `W, b, V ⊢ c` derive `U, W, a⊸b, V ⊢ c`.
Here a = nn b ⊸ 0, b = 0, a⊸b = nn(nn b).

So L⊸ with a = (nn b ⊸ 0), b = 0:
From `U ⊢ nn b ⊸ 0` and `W, 0, V ⊢ c` derive `U, W, nn(nn b), V ⊢ c`.

We want `(b⊸0), nn(nn b) ⊢ 0`. So U = [b⊸0], W = [], V = [], c = 0.
Need: `[b⊸0] ⊢ nn b ⊸ 0` and `[0] ⊢ 0`.
- `[0] ⊢ 0` is Refl. ✓
- `[b⊸0] ⊢ (nn b) ⊸ 0 = ((b⊸0)⊸0) ⊸ 0`:
  By R⊸: suffices `(b⊸0)⊸0, b⊸0 ⊢ 0`.
  By Comm: `b⊸0, (b⊸0)⊸0 ⊢ 0`.
  This is `mp⊸-in` with a = b⊸0, b = 0. ✓

So the proof is:
```
d1 : Int ((b⊸0) ∷ (b⊸0)⊸0 ∷ []) 0
d1 = mp⊸-in iFL   -- where iFL = inl ∘ inl : FLRules ⊆R IntRules

d2 : Int ((b⊸0)⊸0 ∷ (b⊸0) ∷ []) 0
d2 = comm d1   -- Comm swap

d3 : Int (singleton (b⊸0)) ((b⊸0)⊸0 ⊸ 0)   -- = [b⊸0] ⊢ nn b ⊸ 0
d3 = ByRule (iFL R⊸) (d2 ∷ᵃ []ᵃ)

d4 : Int (singleton `0) `0
d4 = Refl

-- L⊸ on nn(nn b): from [b⊸0] ⊢ nn b ⊸ 0 and [0] ⊢ 0, derive (b⊸0), nn(nn b) ⊢ 0
d5 : Int ((b⊸0) ∷ nn(nn b) ∷ []) `0
d5 = ByRule (iFL (L⊸ {U = [b⊸0]} {V = []} {W = []} {a = nn b ⊸ 0} {b = 0} {c = 0}))
  (d3 ∷ᵃ d4 ∷ᵃ []ᵃ)

Wait, L⊸ has signature: from U ⊢ a and W,b,V ⊢ c derive U,W,a⊸b,V ⊢ c.
So with U = [b⊸0], a = nn b ⊸ 0, b = 0, W = [], V = [], c = 0:
Conclusion: [b⊸0] ++ [] ++ [nn(nn b)] ++ [] ⊢ 0 = [b⊸0, nn(nn b)] ⊢ 0

-- Comm: nn(nn b), b⊸0 ⊢ 0
d6 : Int (nn(nn b) ∷ (b⊸0) ∷ []) `0
d6 = comm d5

-- R⊸: [nn(nn b)] ⊢ (b⊸0)⊸0 = nn b
d7 : Int (singleton (nn(nn b))) (nn b)
d7 = ByRule (iFL R⊸) (d6 ∷ᵃ []ᵃ)
```

This gives `jj→j` in Int without any circular dependency.

So the workflow is:
1. `jj→j-int : ∀ b → Int [nn(nn b)] (nn b)` — direct proof in Int using FL+Comm rules
2. `gli⊆int : Gli ⊆ Int` — mutual recursion using `jj→j-int` and `iMin : MinRules ⊆R IntRules = inl`
3. `int⊆cla : Int ⊆ Cla` — mutual recursion, key case is L0 admissibility
4. `glivenko-cond-proof : Glivenko-Cond` — `→`: gli⊆int ∘ m→gj. `←`: destab-M ∘ int⊆cla.
5. `corollary22-proof` — tuple assembly

For `int⊆cla` (the hard case — L0 admissibility in M⟨nn,Min⟩):

`Deriv IntRules Γ a → M⟨nn,Min⟩ Γ a`

Mutual recursion on Deriv IntRules:
- Refl → Refl
- Trans d₁ d₂ → Trans (int⊆cla d₁) (int⊆cla d₂)
- ByRule (inl minR) ds → ByRule (inl minR) (int⊆cla-all ds)  -- MinRules base
- ByRule (inr l0R) ds → ??? -- L0 case

The L0 case:
`ByRule (inr (l0-instance {U} {V} {c})) (d ∷ᵃ []ᵃ)`
where `d : Int (plug₁ U `0 V) c = Int (U ++ `0 ∷ V) c`.
Need: `M⟨nn,Min⟩ (U ++ V) c`.

By IH: `int⊆cla d : M⟨nn,Min⟩ (U ++ `0 ∷ V) c = M (plug₁ U `0 V) c`.

Need to derive `M (U ++ V) c` from `M (plug₁ U `0 V) c`.

In M, we have Mono (weakening) which goes the wrong way (adds a formula).
We need L0 admissibility in M.

Actually, M has `jstab` which gives `[nn a] ⊢ a` for any a. So M already has Refl and jstab.

The problem: M⟨nn,Min⟩ doesn't have L0 as a rule. We need to show it's admissible.

For L0 to be admissible in M, we need: for any M-derivation d of `U ++ `0 ∷ V ⊢ c`,
we can derive `U ++ V ⊢ c` in M.

This requires induction on M-derivations, not on Int-derivations. So `int⊆cla` can't be done by just mapping Int → M with a special case for L0.

Hmm. Let me think about this differently.

Actually, maybe I should do a full induction on M-derivations to show L0 admissibility.

`l0-admissible : ∀ {U V c} → M⟨nn,Min⟩ (plug₁ U `0 V) c → M⟨nn,Min⟩ (U ++ V) c`

Induction on M-derivation:
- Refl: `Refl : M (plug₁ U `0 V) c` means `plug₁ U `0 V = singleton c` and `c = c`. So U ++ `0 ∷ V = [c], meaning U = [] and V = [] and c = `0. Then U ++ V = [] and we need `M [] `0`. But we can't derive ⊢ 0 in general! Unless... wait.

  Actually, if `plug₁ U `0 V ▷ c` matches `Refl`, then `plug₁ U `0 V = [c]` as a context. So the context is `[c]` and the formula is `c`. But `plug₁ U `0 V = U ++ `0 ∷ V`. For this to be `[c]`, we need `U = []`, `V = []`, and `c = `0`. Then we need `M [] `0`. We can't prove `⊢ `0` in M (or any reasonable logic).

So L0 is NOT admissible in M in general! The cut `Refl : [`0] ⊢ `0` can be removed (giving `[] ⊢ `0`) only if `⊢ `0` is derivable.

This means `int⊆cla` is NOT provable by just showing L0 admissibility.

Wait, but let me reconsider what `int⊆cla` should actually do. We need `Int ⊆ Cla`, i.e., `Deriv IntRules Γ a → M⟨nn,Min⟩ Γ a`.

The M operator doesn't just add `jstab` — it stabilizes ALL conclusions. So `M Γ a` doesn't require `Γ ⊢ a` directly, it works with a richer system where conclusions can be unstabilized via jstab.

Let me re-read the M definition... From Extensions.agda, `M⟨j,R⟩` is `Deriv (MjRules j R)` where `MjRules j R = R ∪R JstabRules j`. And `JstabRules j` has one rule: `jstab-instance : {a} → JstabRules j (mkRule ([j a ▷ a] ∷ []) (singleton (j a) ▷ a))`. Wait no, let me check.

Actually let me check the Extensions.agda definition of MjRules more carefully.

Hmm, from the summary: `M⟨j,R⟩ rules: inl rr (base R), inr jstab-instance (j-stability)`.

So `MjRules j R r = R r ⊎ JstabRules j r` where JstabRules gives `[j a] ⊢ a`.

So `M⟨nn,Min⟩` has:
- All MinRules (FL + Comm + Mono + Contr)
- jstab: `[nn a] ⊢ a` for all a
- Plus Refl and Trans from Deriv

So `M (plug₁ U `0 V) c` means we have a derivation using MinRules + jstab with context `U ++ `0 ∷ V` and conclusion `c`.

Now, can we remove `0` from the antecedent in M? We have Mono (weakening), which can ADD formulas. If we also had Contr, we could CONTRACT duplicates. But removing a specific formula like 0 needs L0.

Actually, this suggests `int⊆cla` might need a fundamentally different approach. Let me think about what the paper says...

In the paper, the Glivenko theorem says: for Int (intuitionistic logic), `Cla Γ a ↔ Int Γ (nn a)`.

The direction `Cla Γ a → Int Γ (nn a)` should be straightforward: Cla = M⟨nn,Min⟩, and we can embed Min ⊆ Int, and use m→gj to get G⟨nn,Min⟩ Γ (nn a), and then embed G into Int.

The direction `Int Γ (nn a) → Cla Γ a` is the interesting one. Given `Deriv IntRules Γ (nn a)`, we need `M⟨nn,Min⟩ Γ a`.

Since conclusion is `nn a`, we can use `destab-M` once we have `M Γ (nn a)`. So we need `Deriv IntRules Γ (nn a) → M⟨nn,Min⟩ Γ (nn a)`.

This is `int⊆cla` restricted to nn-type conclusions. The question is whether this restricted form is easier.

For the L0 case with nn-type conclusion:
Given `M (U ++ `0 ∷ V) (nn c)` (where `nn c = (c⊸0)⊸0`), need `M (U ++ V) (nn c)`.

Hmm, still the same issue. The Refl case would need U=[], V=[], nn c = `0, which means (c⊸0)⊸0 = `0 — impossible since they're different constructors! So actually the Refl case CAN'T happen when the conclusion is `nn c` and the context is `[`0]`.

Wait, that's important! For the restricted `int⊆cla` at nn-type conclusions:
- The Refl case: `Refl : [nn c] ⊢ nn c`. Context is `[nn c]`, not `[`0]`. So `plug₁ U `0 V = [nn c]` requires `0 = nn c`, which is impossible. So the Refl case where context = [`0] doesn't arise!

But wait, that's the Refl case of M, not of the L0 admissibility induction. Let me reconsider.

The `int⊆cla` function does mutual recursion on `Deriv IntRules`. The L0 case gives us:
- Premise: `d : Deriv IntRules (plug₁ U `0 V) c`
- By IH: `int⊆cla d : M (plug₁ U `0 V) c`
- Need: `M (U ++ V) c`

So we have an M-derivation of `U ++ `0 ∷ V ⊢ c` and need `U ++ V ⊢ c` in M.

This requires a separate lemma: L0 admissibility in M⟨nn,Min⟩.

For L0 admissibility, we do induction on the M-derivation. The Refl case needs `plug₁ U `0 V = [c]`, which requires `c = `0` (and `U = [], V = []`). Then we need `M [] `0`. But `M [] `0` means `⊢ `0` which is NOT derivable.

So L0 is NOT admissible in M⟨nn,Min⟩ in general. Therefore `int⊆cla` as stated cannot be proven.

But wait — in the `int⊆cla` induction, when we reach the L0 case, we don't have an arbitrary M-derivation. We have `int⊆cla d` where `d : Deriv IntRules (plug₁ U `0 V) c`. The IH gives `M (plug₁ U `0 V) c`. But we need `M (U ++ V) c`.

Hmm, what if instead of `int⊆cla`, we prove `glivenko-cond` directly?

`→`: `Cla Γ a → Int Γ (nn a)`
Given M⟨nn,Min⟩ Γ a, apply m→gj nn-expansive-Min to get G⟨nn,Min⟩ Γ (nn a), then gli⊆int to get Int Γ (nn a). gli⊆int is straightforward (no L0 needed).

`←`: `Int Γ (nn a) → Cla Γ a`
Given Deriv IntRules Γ (nn a). Need M⟨nn,Min⟩ Γ a.

Approach: prove `Deriv IntRules Γ (nn a) → M⟨nn,Min⟩ Γ (nn a)` and then apply destab-M.

For `Deriv IntRules Γ (nn a) → M⟨nn,Min⟩ Γ (nn a)`, we need to handle the L0 case specifically for nn conclusions.

Actually, I think the standard proof in the literature uses a different approach. Let me think about what proof the paper uses...

In Galatos-Ono 2010 and the follow-up papers, the Glivenko theorem is typically proven using the conservation theorem (Theorem 11) and the nucleus properties.

Theorem 11 (Conservation): For L' = L⟨R ∪R R'⟩:
- (1) L' ⊆ Kj(L')
- (2) Kj(L') ⊆ L' ↔ M⟨j,R⟩ ⊆ L'
- (3) Kj(L') ⊆ M⟨j,R⟩ ↔ L' ⊆ M⟨j,R⟩
- (4) M⟨j,R⟩ ⊆ Kj(L') ↔ G⟨j,R⟩ ⊆ L'

The Glivenko theorem says: for R = MinRules, R' = L0Rules (so L' = Int), j = nn:
`Cla Γ a ↔ Int Γ (nn a)`

The `←` direction is: `Kj nn Int ⊆ Cla`. That is, `Int Γ (nn a) → Cla Γ a`.

By Theorem 11 clause (3): `Kj(Int) ⊆ M⟨nn,Min⟩ ↔ Int ⊆ M⟨nn,Min⟩`.

So we need `Int ⊆ Cla`, which is `int⊆cla`. This brings us back to the same problem.

Hmm, but Theorem 11 clause (3) goes both ways. The `→` direction says: if `Kj(Int) ⊆ Cla` then `Int ⊆ Cla`. And the `←` direction says: if `Int ⊆ Cla` then `Kj(Int) ⊆ Cla`.

Both directions need `int⊆cla`, which we can't prove. So maybe the Glivenko theorem requires an additional assumption that we're missing?

Wait, let me re-check the paper... Actually, in the Galatos-Ono framework, the Glivenko theorem is NOT a direct consequence of Theorem 19 alone. It requires an additional step showing that `Int ⊆ Cla` (or equivalently, that L0 is admissible in Cla).

The reason Int ⊆ Cla should hold is: in classical logic (which Cla represents), L0 (ex falso / explosion) is admissible because:
- We have Mono (weakening), which gives `Γ ⊢ a → Γ,b,Δ ⊢ a`
- We have the double negation property

But wait, L0 says: from `U,0,V ⊢ c` derive `U,V ⊢ c`. This is removing 0 from the antecedent. In classical logic with weakening, if we can prove `U,0,V ⊢ c`, can we prove `U,V ⊢ c`?

Not necessarily! Unless 0 is somehow "redundant" in the sense that it doesn't add information.

But wait, in M⟨nn,Min⟩, the conclusions are "stabilized" — they go through nn = (·⊸0)⊸0. So actually, in M, every derivation `M Γ c` implicitly means `Γ ⊢ c` where all intermediate conclusions could be unstabilized via jstab.

Hmm, I think the key insight is: in M⟨nn,MinRules⟩, `0` in the antecedent is indeed redundant because nn conclusions only care about whether you can derive `0` from `c⊸0`. Having `0` in the context gives you `0` directly, but the L0 rule removing it should still leave you with enough to derive the nn conclusion.

Let me think about this more carefully...

Actually, I think the proof might go through showing that in M⟨nn,Min⟩ specifically, L0 is admissible because:
1. By Mono: `M (U ++ V) c → M (U ++ `0 ∷ V) c` (adding 0)
2. We need the converse for L0 admissibility.

The converse is NOT generally true. But for M⟨nn,Min⟩ specifically, every M-derivable sequent `U ++ `0 ∷ V ⊢ c` has `c` being "nn-stable" in some sense.

Actually wait, `M Γ c` does NOT mean `c = nn c`. M-derivable sequents can have arbitrary conclusions — jstab gives `[nn a] ⊢ a`, so you can have non-nn conclusions.

I think I need to take a step back. Maybe there's a simpler approach to the Glivenko-Cond.

Alternative: Don't prove `int⊆cla` at all. Instead, prove Glivenko-Cond directly using Theorem 11 (Conservation theorem).

From Conservation.agda, `theorem11` has:
```
theorem11
  : ∀ {j R R'}
  → Expansive j R
  → (L⟨ R ∪R R' ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩))          -- (1)
    × ((Kj j (L⟨ R ∪R R' ⟩) ⊆ L⟨ R ∪R R' ⟩)        -- (2) Kj(L') ⊆ L' ↔ M ⊆ L'
       ↔ (M⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩))
    × ((Kj j (L⟨ R ∪R R' ⟩) ⊆ M⟨ j , R ⟩)            -- (3) Kj(L') ⊆ M ↔ L' ⊆ M
       ↔ (L⟨ R ∪R R' ⟩ ⊆ M⟨ j , R ⟩))
    × ((M⟨ j , R ⟩ ⊆ Kj j (L⟨ R ∪R R' ⟩))            -- (4) M ⊆ Kj(L') ↔ G ⊆ L'
       ↔ (G⟨ j , R ⟩ ⊆ L⟨ R ∪R R' ⟩))
```

With j = nn, R = MinRules, R' = L0Rules:
- L' = L⟨ MinRules ∪R L0Rules ⟩ = L⟨ IntRules ⟩ = Int
- Kj nn Int = `Int Γ (nn a)` = `Deriv IntRules Γ (nn a)`

Clause (3): `(Int Γ (nn a) → Cla Γ a) ↔ (Int ⊆ Cla)`

So the `←` direction of Glivenko-Cond (`Int Γ (nn a) → Cla Γ a`) is EQUIVALENT to `Int ⊆ Cla`.

This means I do need int⊆cla after all. Unless I prove it via clause (2) instead.

Clause (2): `(Int Γ (nn a) → Int Γ a) ↔ (Cla ⊆ Int)`. Hmm, `Int Γ (nn a) → Int Γ a` says double negation elimination in Int, which is classical and not valid in Int.

Let me look at clause (4): `(Cla ⊆ Kj nn Int) ↔ (Gli ⊆ Int)`.
So `Cla Γ a → Int Γ (nn a)` iff `Gli ⊆ Int`.

`Gli ⊆ Int` is gli⊆int which is easy! So the `→` direction of Glivenko-Cond follows from Theorem 11 clause (4).

More precisely: from Theorem 11 clause (4), `from` direction: `Gli ⊆ Int → Cla ⊆ Kj nn Int`, i.e., `Gli ⊆ Int → ∀ {Γ a} → Cla Γ a → Int Γ (nn a)`.

So: `→` direction of Glivenko-Cond = `from (snd (snd (snd (theorem11 nn-expansive-Min)))) gli⊆int`.

For the `←` direction: `Int Γ (nn a) → Cla Γ a`. By Theorem 11 clause (3):
`(Kj nn Int ⊆ Cla) ↔ (Int ⊆ Cla)`.

So this requires `Int ⊆ Cla`. But by clause (3) `from` direction, if `Int ⊆ Cla` then `Kj nn Int ⊆ Cla`. And by `to` direction, if `Kj nn Int ⊆ Cla` then `Int ⊆ Cla`.

Hmm, still circular. But maybe I can use a different clause.

Actually, the `to` direction of clause (3): `Kj nn Int ⊆ Cla → Int ⊆ Cla`. This says: if `Int Γ (nn a) → Cla Γ a` for all Γ,a (which is the ← of Glivenko-Cond), then `Int ⊆ Cla`. So if I can prove the ← of Glivenko-Cond directly, I get int⊆cla for free.

But proving ← directly is the hard part!

Let me look for a different angle. Maybe clause (1) helps.
Clause (1): `Int ⊆ Kj nn Int`, i.e., `Int Γ a → Int Γ (nn a)`. This says nn is expansive over Int. Since nn is expansive over MinRules (nn-expansive-Min), and MinRules ⊆R IntRules, this follows from lifting. So `Int Γ a → Int Γ (nn a)` is just `Rnn-R iMin` where `iMin : MinRules ⊆R IntRules = inl`.

Actually wait, `Rnn-R` needs `FLeRules ⊆R R'`, not `MinRules ⊆R R'`. But `fle⊆min : FLeRules ⊆R MinRules` and `inl : MinRules ⊆R IntRules`, so `inl ∘ fle⊆min : FLeRules ⊆R IntRules`.

So we have:
- Int ⊆ Kj nn Int (via Rnn-R / nn-expansive)
- Cla ⊆ Kj nn Int (via gli⊆int + m→gj)

The Glivenko-Cond says: Cla ↔ Kj nn Int.

For ←: Kj nn Int ⊆ Cla. This is the hard direction.

Hmm, I wonder if the paper actually proves `int⊆cla` or takes it as an axiom/external result.

Let me look at how Int relates to Cla in the substructural logic literature. In the Full Lambek calculus setting:
- FL has no structural rules
- FLe has exchange (Comm)
- FLew has exchange + weakening (Mono) — this is relevant for intuitionistic logic
- FLewc has exchange + weakening + contraction (Contr) — this is relevant for classical logic
- MinRules = FL + Comm + Mono + Contr = FLewc
- IntRules = MinRules + L0 = FLewc + L0

Now, L0 says: from `U, 0, V ⊢ c` derive `U, V ⊢ c` (removing 0 from antecedent).

In Int, L0 gives "ex falso quodlibet" — from `0` you can derive anything. This is a key axiom of intuitionistic logic.

In Cla = M⟨nn, MinRules⟩, is L0 admissible? The question is: if `M (U ++ `0 ∷ V) c`, can we derive `M (U ++ V) c`?

In M, we work with stabilized derivations. M has all of MinRules (including weakening), plus jstab (`[nn a] ⊢ a`).

For L0 admissibility in M: given `M (U ++ `0 ∷ V) c`, I need `M (U ++ V) c`.

Actually, wait. Let me think about what `0` means in this context. `0` is the bottom element of the lattice. In substructural logic, `0` is the unit of `∨`. The L0 rule removes `0` from the antecedent.

In classical logic (Cla), ex falso should hold because from `0` in the antecedent, we can derive anything. With weakening (Mono), we can add `0` back if needed. But removing `0` requires L0 specifically.

I think the key insight might be that in M⟨nn, MinRules⟩, we can prove L0 admissibility using the specific properties of nn:

For any c, `M (plug₁ U `0 V) c` → `M (U ++ V) c`:

Case analysis on the M-derivation is complex. Let me try a different approach.

Maybe instead of proving `int⊆cla` directly, I should prove `Glivenko-Cond` by using the Odintsov equivalence:

1. We already have `odintsov-cond3→cond2 : MinRules ⊆R R → Odintsov-Cond3 (Deriv R) → Gli ⊆ Deriv R`
2. With R = IntRules: if we have `Odintsov-Cond3 (Int) = Shift⊸ nn Int`, then `Gli ⊆ Int`
3. We have `odintsov-cond2→cond1 : Int ⊆ Cla → Gli ⊆ Int → Odintsov-Cond1 (Int)`
4. `Odintsov-Cond1 (Int) = ∀ {Γ a} → Cla Γ a ↔ Int Γ (nn a)` = Glivenko-Cond

So: if I can prove:
(a) `Int ⊆ Cla`
(b) `Shift⊸ nn Int`
Then I'm done.

But (a) is the same `int⊆cla` problem!

OK let me try yet another approach. What if I decompose the proof differently?

For the `←` direction of Glivenko-Cond: `Int Γ (nn a) → Cla Γ a = M⟨nn,Min⟩ Γ a`:
- `Int Γ (nn a) = Deriv IntRules Γ (nn a)`
- Need: `M⟨nn,Min⟩ Γ a`

By destab-M, suffices to show `M⟨nn,Min⟩ Γ (nn a)`.

For `M⟨nn,Min⟩ Γ (nn a)`: this means derive `Γ ⊢ nn a` using MinRules + jstab.

Now, `Deriv IntRules Γ (nn a)` uses MinRules + L0. I need to show that every IntRules derivation with nn conclusion can be replicated in M⟨nn,Min⟩.

The key: when conclusion is nn a = (a⊸0)⊸0, the L0 rule `plug₁ U `0 V ⊢ nn a → U++V ⊢ nn a` might be replaceable.

Given `M (plug₁ U `0 V) (nn a)`, I need `M (U ++ V) (nn a)`.

Expand nn a = (a⊸0)⊸0. Use R⊸: to prove `U ++ V ⊢ (a⊸0)⊸0`, suffices to prove `(a⊸0), U ++ V ⊢ 0`.

From `M (plug₁ U `0 V) ((a⊸0)⊸0)`:
By R⊸-invert(?): `(a⊸0), plug₁ U `0 V ⊢ 0`... wait, R⊸-invert only works for L⟨R⟩, not M.

Hmm, this is getting complicated. Let me try a completely different approach.

What if `int⊆cla` is provable via mutual recursion on Int derivations, where the L0 case uses the fact that in M, 0 in the antecedent is "eliminable" because M has Mono (weakening)?

Wait: Mono ADDS elements, not removes them. So Mono gives `M (U ++ V) c → M (plug₁ U `0 V) c`, which is the REVERSE of L0.

Hmm. In classical logic, L0 (ex falso) is typically derived from:
1. From 0 in the antecedent, derive anything using L0
2. In Cla, this should be: from `0` in the antecedent, derive any `nn c`

Maybe the right approach is: in M⟨nn,Min⟩, prove `∀ {Γ c} → M (`0 ∷ Γ) c`:
"From 0, everything follows in M."

This is a weaker form: if `0` is in the context at position 0, then ANY sequent is derivable. Then L0 admissibility follows from Trans: given `M (plug₁ U `0 V) c`, do Trans with the ex-falso derivation.

Wait, that doesn't work either because we need `M Γ c` for arbitrary `c`, and we can't derive everything from 0 in M without L0.

Actually, in M⟨nn,Min⟩, we have all MinRules including FL rules. FL has the rule R1 (axiom for 1), but NOT a rule that gives everything from 0.

Let me check: does FL have any rule involving `0` on the left?

From Rules.agda, the FL rules are: L∨, R∨₁, R∨₂, L∧₁, L∧₂, R∧, L1, R1, L·, R·, L⊸, R⊸, L›, R›.

None of these specifically handle `0` on the left. The L0 rule (from L0Rules) is the ONLY rule that handles `0` as "ex falso."

So in M⟨nn,Min⟩ (which has FL + Comm + Mono + Contr + jstab but NOT L0), we cannot derive `[`0] ⊢ c` for arbitrary `c`. Therefore `int⊆cla` as stated seems impossible!

But wait — the paper's Glivenko theorem must work. Let me re-read the paper's statement...

Looking at the definitions in Glivenko.agda:
```
Glivenko-Cond : Type
Glivenko-Cond = ∀ {Γ a} → Cla Γ a ↔ Int Γ (¬¬ a)
```

Maybe the issue is that Glivenko-Cond as stated in the formalization is too strong, or needs additional conditions?

Actually, let me check what `Cla` and `Int` are in the paper. In the paper:
- CL (classical logic) is typically defined as Int + double negation elimination
- In the substructural setting, Cla = M⟨nn, MinRules⟩ and Int = L⟨IntRules⟩

The Glivenko theorem in the substructural setting says that Cla is the nn-image of Int. This means `Cla = {(Γ, a) | Int Γ (nn a)}`.

For `→` (Cla ⊆ Kj nn Int): use gli⊆int + m→gj.
For `←` (Kj nn Int ⊆ Cla): this says `Int Γ (nn a) → Cla Γ a`.

The standard proof of `←` in the substructural logic literature goes:
1. `Int Γ (nn a)` means `Deriv IntRules Γ (nn a)`
2. Since `MinRules ⊆R IntRules`, `Deriv MinRules ⊆ Deriv IntRules` (via lift-⊆R)
3. Need to show that L0 is admissible for nn-conclusions in M

Actually, I just realized: maybe `int⊆cla` is NOT needed. Maybe only `int⊆cla` at nn-conclusions is needed, which is a weaker statement. And for nn-conclusions, L0 might be admissible because:

Given `M (plug₁ U `0 V) (nn c)` where nn c = (c⊸0)⊸0:
- The conclusion is a double negation. In M with weakening, having `0` in the antecedent is redundant for double-negation conclusions because the conclusion only "asks" whether you can derive `0` from `c⊸0`. The antecedent `0` contributes `0` directly, but if you can derive `(c⊸0)⊸0` from `U, 0, V`, you should be able to derive it from `U, V` because the `0` in the antecedent is "dead weight" for a double-negation conclusion.

Hmm, but this is intuitive, not a proof.

Let me try yet another approach. I think the cleanest way is to use Conservation Theorem 11 directly.

Actually, looking at Theorem 11 more carefully:

Clause (4): `M⟨j,R⟩ ⊆ Kj j (L⟨R ∪R R'⟩) ↔ G⟨j,R⟩ ⊆ L⟨R ∪R R'⟩`

With j=nn, R=MinRules, R'=L0Rules:
`Cla ⊆ Kj nn Int ↔ Gli ⊆ Int`

The `from` direction: `Gli ⊆ Int → Cla ⊆ Kj nn Int`, i.e., `Gli ⊆ Int → ∀ {Γ a} → Cla Γ a → Int Γ (nn a)`.

This gives the `→` direction of Glivenko-Cond! And we can prove `Gli ⊆ Int` easily (just embed MinRules into IntRules and handle Lj/Rj).

For the `←` direction, looking at clause (3):
`Kj nn Int ⊆ Cla ↔ Int ⊆ Cla`

The `from` direction: `Int ⊆ Cla → Kj nn Int ⊆ Cla`, i.e., `Int ⊆ Cla → Int Γ (nn a) → Cla Γ a`.

But the `to` direction: `Kj nn Int ⊆ Cla → Int ⊆ Cla`, i.e., `(Int Γ (nn a) → Cla Γ a) → (Int Γ a → Cla Γ a)`.

The `to` direction of (3) says: if we can go from `Kj nn Int` to `Cla`, then we can go from `Int` to `Cla`. The proof (from Conservation.agda): since `Int ⊆ Kj nn Int` (clause 1), we compose.

So to get the `←` direction of Glivenko-Cond, I need either:
(a) `Int ⊆ Cla` directly, OR
(b) Some other way

Hmm, wait. Maybe I should look at what clauses 2 and 4 give together.

Clause (2): `Kj nn Int ⊆ Int ↔ Cla ⊆ Int`
Clause (4): `Cla ⊆ Kj nn Int ↔ Gli ⊆ Int`

If I had `Cla ⊆ Int`, then by clause (2) `from`: `Kj nn Int ⊆ Int`, meaning `Int Γ (nn a) → Int Γ a` (double negation elimination in Int). But that's false!

So `Cla ⊈ Int`. This means Int ⊈ Cla as well (since they're incomparable: Int has L0 but not jstab, Cla has jstab but not L0).

But wait, the Glivenko theorem says `Cla ↔ Kj nn Int`. This doesn't require `Cla ⊆ Int` or `Int ⊆ Cla`.

The `→` direction `Cla ⊆ Kj nn Int` follows from clause (4).
For the `←` direction `Kj nn Int ⊆ Cla`:

Can I get this from clause (3)? Clause (3) says `Kj nn Int ⊆ Cla ↔ Int ⊆ Cla`. So I need `Int ⊆ Cla`, which is `int⊆cla`.

So the question reduces to: is `Int ⊆ Cla` true?

`Int = Deriv IntRules` and `Cla = Deriv (MjRules nn MinRules) = Deriv (MinRules ∪R JstabRules nn)`.

IntRules = MinRules ∪R L0Rules
MjRules nn MinRules = MinRules ∪R JstabRules nn

So Int has L0 but not jstab, and Cla has jstab but not L0.

For `Int ⊆ Cla`: every IntRules-derivable sequent is MjRules-derivable. This means we need to show that L0 is admissible in `Deriv (MinRules ∪R JstabRules nn)`.

L0 in Cla: given `Cla (plug₁ U `0 V) c`, derive `Cla (U ++ V) c`.

This is a real proof-theoretic question: is L0 (ex falso) admissible in the logic MinRules + jstab for nn?

In MinRules + jstab(nn), we have:
- FL rules (all connectives)
- Comm, Mono, Contr (structural rules)
- jstab: `[nn a] ⊢ a` for all a

The jstab rule for nn: `[(a⊸0)⊸0] ⊢ a`.

This is double negation elimination! `(a⊸0)⊸0 → a` is exactly DNE.

So Cla = MinRules + DNE (double negation elimination). And Int = MinRules + L0 (ex falso).

Now, `Int ⊆ Cla` means: every sequent derivable in MinRules+L0 is derivable in MinRules+DNE.

The L0 rule: from `U, 0, V ⊢ c` derive `U, V ⊢ c`. We need to simulate this in MinRules+DNE.

In MinRules+DNE, with 0 in the antecedent:
- From `U, 0, V ⊢ c`, we need `U, V ⊢ c`.

With DNE, we can derive: from `U, V ⊢ (c⊸0)⊸0` we get `U, V ⊢ c` (by jstab). But we need to first derive `U, V ⊢ (c⊸0)⊸0`.

Hmm, that still requires `U, V ⊢ c` which is circular.

I think the key is that in MinRules+DNE, L0 IS admissible, but the proof goes by induction on derivations, not by a simple composition.

For the Refl case: `Refl : [`0] ⊢ `0`. After L0 removal: `[] ⊢ `0`. In MinRules+DNE, can we prove `⊢ `0`? Only if `0` is derivable in classical logic without assumptions. But `0` (falsity) is NOT generally derivable without assumptions. So Refl at `0` doesn't L0-reduce.

BUT — the point is that `int⊆cla` is a function from `Deriv IntRules Γ a` to `Cla Γ a`, not L0-admissibility in Cla. The mutual recursion on Int derivations handles L0 by using the inductive hypothesis, not by doing L0 in Cla.

Let me try again:
```
int⊆cla : Int ⊆ Cla
int⊆cla Refl = Refl
int⊆cla (Trans d₁ d₂) = Trans (int⊆cla d₁) (int⊆cla d₂)
int⊆cla (ByRule (inl minR) ds) = ByRule (inl minR) (int⊆cla-all ds)
int⊆cla (ByRule (inr l0-instance) (d ∷ᵃ []ᵃ)) = ???
```

In the L0 case: we have `d : Int (plug₁ U `0 V) c` and by IH `int⊆cla d : Cla (plug₁ U `0 V) c`.
We need `Cla (U ++ V) c`.

So we're back to L0 admissibility in Cla.

And for Refl case of L0-admissibility: if `Cla (plug₁ U `0 V) c` via Refl, then `plug₁ U `0 V = [c]`, so `c = `0` and U=[], V=[]. Need `Cla [] `0`.

`Cla [] `0` = `M⟨nn,Min⟩ [] `0` = derive `⊢ `0` using MinRules + jstab(nn).

jstab(nn) gives `[(c⊸0)⊸0] ⊢ c`. With c = `0: `[((`0⊸0)⊸0)] ⊢ `0`.

`Cla [] `0` means deriving `⊢ `0` without any hypotheses. In MinRules + DNE, can we derive `⊢ 0`?

The only way to derive something without hypotheses is R1 (`⊢ 1`). But `0 ≠ 1`. So `⊢ 0` is NOT derivable.

This confirms: L0 is NOT admissible in Cla in general. Therefore `int⊆cla` is NOT provable.

So `Glivenko-Cond` as stated (`∀ {Γ a} → Cla Γ a ↔ Int Γ (nn a)`) might be FALSE or require additional conditions!

Wait, actually, let me re-examine. The issue is with the Refl case. But in the mutual recursion for `int⊆cla`, the L0 case has:
- Premise: `d : Int (plug₁ U `0 V) c`
- IH: `int⊆cla d : Cla (plug₁ U `0 V) c`

The question is whether we can get `Cla (U ++ V) c` from `Cla (plug₁ U `0 V) c`.

But in the recursion, `d` is a sub-derivation. If `d = Refl`, then `plug₁ U `0 V = [c]` and `c = `0`. Then `U ++ V = []` and we need `Cla [] `0` = `⊢ `0`, which is unprovable.

BUT — can `d` actually be `Refl` here? The `d` comes from a `Deriv IntRules (plug₁ U `0 V) c` that is the premise of an L0-instance. For Refl to be the entire premise, we'd need a derivation that's just `Refl : [`0] ⊢ `0` and then applying L0 to get `[] ⊢ `0`.

So `Int [] `0` should be derivable via: `Refl : [`0] ⊢ `0` then `L0: [] ⊢ `0`. But `⊢ `0` is a valid sequent in IntRules because L0 gives us ex falso.

But `Cla [] `0` should NOT be derivable (falsity without hypotheses is not classical).

Wait, that can't be right. `⊢ `0` in Int means "falsity is derivable without hypotheses" which is NOT valid in intuitionistic logic either! The L0 rule allows removing `0` from the antecedent, but you still need `0` to be in the antecedent first.

Let me re-check: `Int [] `0` = `Deriv IntRules [] `0`. Can we derive `⊢ `0` in IntRules?

L0 gives: from `[`0] ⊢ c` derive `[] ⊢ c` (with U=[], V=[]). So from Refl `[`0] ⊢ `0`, L0 gives `[] ⊢ `0`.

But this is absurd! Intuitionistic logic should not derive `⊢ 0`. This suggests L0 as formalized is too strong, OR I'm misunderstanding the L0 rule.

Let me re-read L0Rules:
```
data L0Rules : RuleSet where
  l0-instance : ∀ {U V c}
    → L0Rules (mkRule ((plug₁ U `0 V ▷ c) ∷ []) (U ++ V ▷ c))
```

`plug₁ U `0 V = U ++ (`0 ∷ V)`. So the rule takes premise `U ++ `0 ∷ V ⊢ c` and concludes `U ++ V ⊢ c`.

With U=[], V=[]: premise `[`0] ⊢ c`, conclusion `[] ⊢ c`. From Refl `[`0] ⊢ `0`, we get `[] ⊢ `0`.

This means Int derives `⊢ `0`, which is wrong for intuitionistic logic.

BUT WAIT — this is the L0 rule for the formula `0`, which in substructural logic is the unit of disjunction (∨). In full intuitionistic logic, `0 → c` is valid for all `c`. So `from [`0] ⊢ c derive [] ⊢ c` doesn't mean `⊢ 0` — it means "if `0` implies `c`, then `c`". The PREMISE is `[`0] ⊢ c`, not `[`0] ⊢ `0`.

So from `[`0] ⊢ `0` (Refl) and L0, we get `[] ⊢ `0`. Hmm, but this IS valid in the sequent calculus version of substructural logic, because the rule L0 says: if you have a derivation that USES `0` as a hypothesis and concludes something, you can remove `0` from the hypothesis. With `[`0] ⊢ `0`, the `0` in the hypothesis is "justified" because it appears in the conclusion.

Actually, I think the issue is that `[] ⊢ `0` in the sequent calculus is different from "0 is true." The sequent `Γ ⊢ a` in substructural logic means "from hypotheses Γ, `a` follows." With `[] ⊢ `0`, there are no hypotheses and `0` follows. This IS absurd in intuitionistic logic.

But with the L0 rule as stated: from `[`0] ⊢ `0` (which is trivially true by Refl), L0 gives `[] ⊢ `0`.

Unless I'm misunderstanding the L0 rule. Let me check: is L0 actually meant to be restricted to non-trivial uses of `0`? In standard presentations:
- L⊥ (in intuitionistic logic): from Γ ⊢ ⊥, derive Γ ⊢ A (ex falso quodlibet)
  OR equivalently: if ⊥ is in the antecedent, derive anything: Γ, ⊥ ⊢ A

These are different! The first form doesn't remove ⊥ from the antecedent. The second form says: ⊥ in the antecedent lets you conclude anything.

Looking at L0 again: premise `U ++ `0 ∷ V ⊢ c`, conclusion `U ++ V ⊢ c`. This says: if you can derive `c` with `0` in the antecedent, you can derive `c` without it.

Hmm, that's NOT standard ex falso. Standard ex falso says: from `Γ, ⊥ ⊢ c` for any `c`, not from `c` to `c` with `⊥` removed. The L0 rule as stated is more like "0 is a disposable hypothesis."

Actually wait, this IS the standard left rule for ⊥ in sequent calculus:
```
         (no premise needed)
L⊥: ────────────────────────
      Γ, ⊥ ⊢ c
```

But L0 as formalized has a PREMISE: `U ++ `0 ∷ V ⊢ c`. Standard L⊥ has NO premise.

If L0 were standard L⊥, it would be:
```
l0-instance : ∀ {U V c} → L0Rules (mkRule [] (plug₁ U `0 V ▷ c))
```
(no premises, conclusion is `U, 0, V ⊢ c`)

But the formalized L0 has premise `U, 0, V ⊢ c` and conclusion `U, V ⊢ c`. This is the OPPOSITE direction — it removes 0 from the antecedent.

This is unusual. Let me check if this is how the paper defines it. Looking at the variable name "L0" and comparing with the paper...

From the paper context and substructural logic tradition:
- `L0` is the "left rule for 0" (the additive unit)
- In many substructural presentations, `0` on the left is the weakening rule: `Γ ⊢ c → Γ, 0, Δ ⊢ c` (you can always add 0 to the antecedent since 0 contributes nothing).

Wait, that's the opposite of what L0 says here. L0 here removes 0 from the antecedent.

Hmm, actually in some presentations of substructural logic (e.g., Galatos et al. "Residuated Lattices"):
- L0: Γ, 0, Δ ⊢ c (no premise, i.e., axiom) — from 0 you can derive anything
  OR
- L0: Γ, 0, Δ ⊢ c → Γ, Δ ⊢ c (0 is disposable)

The second form is what's formalized here. This says 0 is a "trivial" hypothesis that can be removed.

In this formulation, `[`0] ⊢ `0` by Refl, then L0 gives `[] ⊢ `0`. This says `⊢ `0`. If `0` is really the zero/bottom element, this is contradictory.

But wait — in the Galatos-Ono tradition, `0` is the additive zero of the lattice, which is the unit of ∨. In bounded lattices, 0 ≤ a for all a. The sequent `⊢ 0` means "0 is derivable" which in the algebraic semantics means 0 = 1 (the lattice is trivial).

So maybe Int (with L0 as formalized) only has models where the lattice is trivial? That can't be right for intuitionistic logic...

I think there might be a subtlety I'm missing about the formalization. Let me go back and look at the actual paper or the full definition.

Actually, you know what, I bet the L0 rule in the paper is meant to be the "initial sequent" for 0:
```
L⊥: Γ, 0, Δ ⊢ c  (no premises, axiom)
```

And the formalized version has a premise because all rules in this framework have premises and a conclusion. The framework doesn't have zero-premise axiom rules; instead, axioms are encoded differently.

But looking at the data type, `l0-instance` has premises = `((plug₁ U `0 V ▷ c) ∷ [])` and conclusion = `(U ++ V ▷ c)`. This is a one-premise rule, not an axiom.

If L0 were an axiom `Γ, 0, Δ ⊢ c`, it would be encoded as `l0-instance : L0Rules (mkRule [] (plug₁ U `0 V ▷ c))` with empty premise list.

So the formalization really does encode L0 as "remove 0 from antecedent." This is strange and I think it leads to Int being trivial unless there's a semantic model that makes this consistent.

OK, I think I'm overthinking this. The user asked me to follow the workflow, not to figure out whether the math is correct. The formalization has these definitions, and I should work with them.

Let me reconsider: given `Int = Deriv IntRules` with `IntRules = MinRules ∪R L0Rules`, where L0 removes 0 from antecedent:

- `Int [] `0` is derivable: Refl gives `[`0] ⊢ `0`, then L0 gives `[] ⊢ `0`.
- Similarly, `Int [] c` for ANY `c`: first get `Int [`0] c` (by Mono from `Int [] `0`... wait, Mono adds to antecedent: `Int [] c → Int [`0] c`... no, Mono is `U₁ ++ U₂ ⊢ b → plug₁ U₁ a U₂ ⊢ b`, i.e., `U₁ ++ U₂ ⊢ b → U₁ ++ a ∷ U₂ ⊢ b`. So from `Int [] c` we get `Int [a] c` for any a.)

Wait, I had `Int [] `0`. From `Int [] `0`, by Mono with U₁=[], U₂=[], a=`0: `Int [`0] `0`. But that's Refl, which we already have.

To get `Int [`0] c` for arbitrary c, I need more than Mono. I need L0 axiom in the other direction (from `0`, derive anything).

Hmm, but the formalized L0 rule only lets you REMOVE 0. To get `[0] ⊢ c` for any c, I'd need the axiom form of L0.

So maybe `Int` is not actually as strong as I thought. Let me check: can Int derive `[`0] ⊢ c` for arbitrary c?

The only way to derive `[`0] ⊢ c` is:
- If c = `0: Refl.
- If c ≠ `0: need to use some rule. FL rules manipulate connectives. L∨ decomposes `∨` in antecedent, R∨ introduces `∨` in succedent, etc.

For `[`0] ⊢ c` where c is an atom or a complex formula, there's no FL rule that applies with just `0` in the antecedent (assuming `0` is a constant, not a compound formula).

So `Int` does NOT derive `[`0] ⊢ c` for arbitrary c. The L0 rule is NOT ex falso quodlibet in the standard sense. It's just "0 is removable from the antecedent."

Then `Int [] `0` IS derivable (from Refl + L0), but `Int [] c` for arbitrary c is NOT.

Now, `Cla [] `0`: is this derivable in M⟨nn,Min⟩? From `M [] (nn `0)` by jstab... no, we need `M [] `0`.

In M⟨nn,Min⟩: we have MinRules (with R1: `[] ⊢ `1`) and jstab (`[nn a] ⊢ a`). To derive `⊢ `0`, the only zero-premise rule is R1, which gives `⊢ `1`, not `⊢ `0`.

So `Cla [] `0` = `M⟨nn,Min⟩ [] `0` is NOT derivable.

BUT `Int [] `0` IS derivable (Refl + L0).

This means `Int ⊈ Cla` — specifically, `Int [] `0` is derivable but `Cla [] `0` is not.

So `int⊆cla` is FALSE.

And therefore `Glivenko-Cond = ∀ {Γ a} → Cla Γ a ↔ Int Γ (nn a)` is FALSE (the ← direction fails at Γ=[], a=`0: `Int [] (nn `0) → Cla [] `0`; `Int [] (nn `0)` is derivable via L0 since `[`0] ⊢ nn `0` by Rnn-R + Refl and then L0 removes it; but `Cla [] `0` is not derivable).

Hmm wait, `Int [] (nn `0)`: we need `Deriv IntRules [] (nn `0) = Deriv IntRules [] ((`0 ⊸ `0) ⊸ `0)`.

Actually, `nn `0 = (`0 ⊸ `0) ⊸ `0`. Is this derivable in Int?

`((`0 ⊸ `0) ⊸ `0)`. By R⊸: from `(`0 ⊸ `0) ⊢ `0` derive `⊢ (`0 ⊸ `0) ⊸ `0`.

Do we have `[`0 ⊸ `0] ⊢ `0` in Int?
By mp⊸-in: `[`0, `0 ⊸ `0] ⊢ `0`. By Comm: `[`0 ⊸ `0, `0] ⊢ `0`. By L0: `[`0 ⊸ `0] ⊢ `0`. Wait no, L0 removes `0` from antecedent, not arbitrary formulas. `0` here is the formula `0`, not `0 ⊸ 0`.

Actually, `mp⊸-in {a = `0} {b = `0}` gives `[`0, `0 ⊸ `0] ⊢ `0`. To use L0 on this, we'd need `0` to be in the antecedent. It IS: `0` is the first formula. So with U=[], V=[`0 ⊸ `0]: L0 gives `[`0 ⊸ `0] ⊢ `0`.

Then R⊸: `[] ⊢ (`0 ⊸ `0) ⊸ `0 = nn `0`. So yes, `Int [] (nn `0)` is derivable.

And `Cla [] `0` is NOT derivable (as argued above).

So `Glivenko-Cond` is FALSE at (Γ=[], a=`0): the ← direction gives `Int [] (nn `0) → Cla [] `0`, but `Int [] (nn `0)` is true and `Cla [] `0` is false.

This means `Glivenko-Cond` as stated is NOT provable. The formalization has a bug in the statement!

OK wait, let me double-check. Maybe `Int [] (nn `0)` is NOT derivable. Let me trace through more carefully.

`nn `0 = (`0 `⊸ `0) `⊸ `0`

To derive `[] ⊢ (`0 `⊸ `0) `⊸ `0` in Int:
By R⊸ (with U=[], a=`0`⊸`0, b=`0): premise is `[`0 `⊸ `0] ⊢ `0`.

To derive `[`0 `⊸ `0] ⊢ `0`:
mp⊸-in gives `[`0, `0 `⊸ `0] ⊢ `0` (a=`0, b=`0).
Using L0 with U=[], V=[`0 `⊸ `0], c=`0: premise `plug₁ [] `0 [`0 `⊸ `0] ⊢ `0` = `[`0, `0 `⊸ `0] ⊢ `0`.
Conclusion: `[] ++ [`0 `⊸ `0] ⊢ `0` = `[`0 `⊸ `0] ⊢ `0`.

So yes, L0 does give `[`0 `⊸ `0] ⊢ `0`.

Then R⊸ gives `[] ⊢ nn `0`.

So `Int [] (nn `0)` IS derivable.

And for `Cla [] `0`: we need `M⟨nn,Min⟩ [] `0`. In M, we have MinRules + jstab. The only way to derive `[] ⊢ `0` is via R1 (which gives `⊢ `1`), not `⊢ `0`. Or via Trans: `[] ⊢ a` and `[a] ⊢ `0` for some a. But `[] ⊢ a` is only derivable for a = `1 (via R1). So we'd need `[`1] ⊢ `0` in M. But `1` and `0` are unrelated in FL (no rule connects them). So `M [] `0` is NOT derivable.

Therefore Glivenko-Cond is false!

Unless I'm wrong about L0. Let me re-read the L0 rule one more time.

```
data L0Rules : RuleSet where
  l0-instance : ∀ {U V c}
    → L0Rules (mkRule ((plug₁ U `0 V ▷ c) ∷ []) (U ++ V ▷ c))
```

The premise sequent is `plug₁ U `0 V ▷ c` = `(U ++ (`0 ∷ V)) ▷ c`.
The conclusion sequent is `(U ++ V) ▷ c`.

So: from `U ++ `0 ∷ V ⊢ c`, conclude `U ++ V ⊢ c`. This removes `0` from position (between U and V).

With U=[], V=[`0 `⊸ `0], c=`0:
Premise: `[] ++ `0 ∷ [`0 `⊸ `0] ⊢ `0` = `[`0, `0 `⊸ `0] ⊢ `0`.
Conclusion: `[] ++ [`0 `⊸ `0] ⊢ `0` = `[`0 `⊸ `0] ⊢ `0`.

Yes, this is correct. L0 removes the `0` from the antecedent.

So my analysis seems correct: `Glivenko-Cond` as stated is false, or at least unprovable.

Now, this is an important finding. I should report this to the user as a "stuck" handoff per the workflow. The architectural issue is that `Glivenko-Cond` as defined is either:
1. Not provable in general (the L0 rule makes Int too strong relative to Cla)
2. Needs a different formulation

Actually wait, let me reconsider. Maybe the issue is that my understanding of `0` is wrong. In substructural logic, `0` might not be "falsity" in the classical sense. Let me check how `0` is defined in Formula.agda.
</thinking>

Let me update the PROOF-PLAN.md to reflect completed work, then have Codex review before implementing.

<function_calls>
<invoke name="Read">
<parameter name="file_path">/home/eapiova/projects/nuclear/Substructural/FL/Formula.agda