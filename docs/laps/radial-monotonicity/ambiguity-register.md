---
name: radial-monotonicity-ambiguity-register
description: Ambiguity register for the radial-monotonicity campaign (RM-00 through RM-02)
metadata:
  type: reference
---

# Ambiguity Register — Radial Term Monotonicity

**Task slug:** `radial-monotonicity`

---

## Summary Table

| ID | Title | Affects | Status |
|---|---|---|---|
| AMB-RM-001 | `hdenPos` vs. `denominatorNonzero` — positivity vs. nonzero | hypothesis design | Resolved by design |
| AMB-RM-002 | `numFun` / `denFun` as API defs vs. proof-internal | module design | Resolved by design |
| AMB-RM-003 | Exact Mathlib lemma for squaring injectivity on non-negatives | proof detail | Resolved: `pow_left_inj₀` |
| AMB-RM-004 | `deriv` vs. `HasDerivAt` interface for `strictMonoOn_of_deriv_pos` | proof strategy | Resolved: `HasDerivAt.deriv` |

---

## AMB-RM-001: `hdenPos` vs. `denominatorNonzero`

**Description:**

`denominatorNonzero k r` asserts D(r) ≠ 0. The monotonicity proof needs D(r) > 0 to
ensure the derivative (a quotient with D(r)² in the denominator) is positive. Under
k2,k4,k6 ≤ 0, D is continuous, D(0) = 1 > 0, so if D(r) ≠ 0 on [0,∞) then D(r) > 0
by IVT. However, making this IVT argument in Lean adds proof complexity.

**Resolution (by design, 2026-05-25):**

Use `hdenPos : ∀ r, 0 ≤ r → 0 < 1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6` directly.
This is strictly stronger than `denominatorNonzero` but avoids the IVT sub-argument.
Callers who have `denominatorNonzero` can supply the stronger `hdenPos` hypothesis
(which implies `denominatorNonzero`). The relationship is documented.

**Status:** Resolved by design (2026-05-25).

---

## AMB-RM-002: `numFun` / `denFun` as API defs vs. proof-internal

**Description:**

The proof rewrites `radialScale k r * r` as `numFun k r / denFun k r` where
`numFun k r = r + k.k1*r^3 + k.k3*r^5 + k.k5*r^7` and
`denFun k r = 1 + k.k2*r^2 + k.k4*r^4 + k.k6*r^6`.
Question: should these be exported project definitions or kept proof-internal?

**Resolution (by design, 2026-05-25):**

Proof-internal only (`let` bindings inside the theorem proof, or `private def`).
They are not semantically interesting as standalone definitions — `numFun` is just
`r * N(r)` and `denFun` is just `D(r)` from the existing spec model. Exporting them
would clutter the project API with redundant definitions.

**Status:** Resolved by design (2026-05-25).

---

## AMB-RM-003: Exact Mathlib lemma for squaring injectivity on non-negatives

**Description:**

RM-02 needs: `0 ≤ a → 0 ≤ b → a^2 = b^2 → a = b`. The candidate Mathlib lemma is
`sq_left_inj` or `pow_left_injective`. The exact name and signature need verification
during implementation.

**Resolution (2026-05-25):**

The correct lemma is `pow_left_inj₀` in
`Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic`:
```
lemma pow_left_inj₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b
```
Used as `(pow_left_inj₀ hf₁ hf₂ two_ne_zero).mp hSq`.

**Status:** Resolved (2026-05-25).

---

## AMB-RM-004: `deriv` vs. `HasDerivAt` interface for `strictMonoOn_of_deriv_pos`

**Description:**

`strictMonoOn_of_deriv_pos` requires `0 < deriv f x` (using Lean's `deriv`), not
`HasDerivAt f d x` directly. The connection is:
`HasDerivAt f d x → deriv f x = d` (via `HasDerivAt.deriv`).

So the proof of `0 < deriv f x` goes:
1. Prove `HasDerivAt f d x` (where d > 0)
2. Rewrite `deriv f x = d` via `HasDerivAt.deriv`
3. Conclude `0 < deriv f x`

The concern: `HasDerivAt.deriv` gives `HasDerivAt f f' x → deriv f x = f' x`, but the
exact Lean name in Lean 4 Mathlib may differ (`HasDerivAt.deriv` or `.hasDerivAt`).

**Resolution (2026-05-25):**

`HasDerivAt.deriv` is confirmed at `Mathlib.Analysis.Calculus.Deriv.Basic:435`:
```
theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f'
```
Used as `rw [h_quot.deriv]` to rewrite `deriv f r` to the explicit quotient-rule value,
then `div_pos` closes the positivity goal.

**Status:** Resolved (2026-05-25).
