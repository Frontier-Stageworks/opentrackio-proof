---
name: inverse-approx-error-capsule
description: Proof capsule for inverse_approx_error_vs_preimage and inverse_approx_exists_unique_with_error, bounding the one-step approximate inverse's error relative to a true preimage
metadata:
  type: project
---

# Proof Capsule — Approximate-Inverse Error Relative to a True Preimage

## Intent (plain English)

Direct continuation of `inverse_approximation/InverseApproximation.lean`
(same file, append-only, no new directory/lean_lib). Two theorems with a
deliberate dependency shape:

1. **`inverse_approx_error_vs_preimage`** — load-bearing, self-contained,
   no Banach/existence machinery. Given a genuine preimage `z` of `y`
   under `D θ t` (hypothesis `hDz : D θ t z = y`, not derived — supplied),
   bound how far the *first-order approximate* inverse `U θ t y` is from
   the *true* `z`, by the standard Banach a priori estimate shape
   `q·|t|·M / (1-q)` where `q = |t|·L θ R`.
2. **`inverse_approx_exists_unique_with_error`** — thin corollary. Get
   existence/uniqueness of `z` from `D_exists_unique_preimage` (existing,
   read-only), then attach the error bound from theorem 1 to that `z`.
   Existence machinery is used *only* here.

This closes a gap the existing `D_exists_unique_preimage` left open: it
proves a `z` exists and is unique, but says nothing about how close the
cheap, non-iterative first-order approximation `U θ t y` is to that exact
`z`. `inverse_approx_error` (already in the file) bounds the round-trip
residual `‖U θ t (D θ t x) - x‖` for an *arbitrary* `x`; the new theorem 1
bounds `‖U θ t y - z‖` where `z` is specifically *the* preimage of a given
`y` — same quantity in the case `y = D θ t x`, but framed the other
direction (from `y`, not from `x`), which is what a caller who only has
`y` (and knows a preimage exists) actually needs.

## Target theorems (user-specified, exact)

```lean
theorem inverse_approx_error_vs_preimage
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y z : ℂ) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hDz : D θ t z = y) :
    ‖U θ t y - z‖ ≤ (|t| ^ 2 * L θ R * M θ R) / (1 - |t| * L θ R)

theorem inverse_approx_exists_unique_with_error
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y : ℂ) (hy : ‖y‖ + |t| * M θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y ∧
      ‖U θ t y - z‖ ≤ (|t| ^ 2 * L θ R * M θ R) / (1 - |t| * L θ R)
```

## Pre-implementation finding: a tighter bound is directly available

Hand-derivation before any Lean code (see `statement-audit.md` for the
full chain): steps 1–4 of the user's own prescribed outline (unfold
`hDz` to get `z = inverseStep θ t y z`, note `U θ t y = inverseStep θ t y y`
definitionally, apply `inverse_step_lipschitz` at `(a,b) = (y,z)`, bound
`‖y-z‖ ≤ |t|·M θ R` via `phi_bounded` at `z`) already give
`‖U θ t y - z‖ ≤ |t|² · L θ R · M θ R` **directly, with no denominator, and
without using `hcontract` at all**. Since `0 < 1 - q < 1` (from
`hcontract`), `a ≤ a/(1-q)` for any `a ≥ 0`, so this tighter bound
trivially implies the user's stated (weaker) target.

This is flagged, not silently acted on. The user's prescribed derivation
(triangle inequality through `‖y - U θ t y‖`, rearrangement, division by
`1-q`) is the *general* Banach a priori estimate pattern — it does not
lean on `hDz` being an *exact* equality the way the shortcut does (the
shortcut's step 1, `z = inverseStep θ t y z`, is only available because
`hDz` gives exact equality; a version of this theorem with an approximate
`hDz` would need the triangle-inequality route). Given the user wrote out
the exact rearrangement in detail and asked for the division step
specifically to be scratch-tested, this reads as a deliberate choice to
establish the general-purpose derivation pattern here, not an oversight.
**Decision: implement exactly the prescribed derivation** (this is what
actually produces the required proof artifact either way — both routes
prove the same target statement), and record the tighter bound as an
explicit finding here for the user's awareness, not as a substituted proof.

## Allowed changes

- Append `inverse_approx_error_vs_preimage` and
  `inverse_approx_exists_unique_with_error` to
  `InverseApproximation.lean`, in that order.
- Small local `have`s inside their proofs.
- `inverse_approximation/README.md`, `docs/specification-questions.md`
  SQ-CV-07: short additive notes, per the user's instruction.

## Forbidden changes

- No edit to any existing declaration in `InverseApproximation.lean`.
- No reopening/strengthening of `phi_bounded`/`phi_lipschitz`/
  `radial_bounded`/`radial_lipschitz`.
- No `CompleteSpace`/`ContractingWith.exists_fixedPoint'`/any existence
  machinery inside `inverse_approx_error_vs_preimage`'s proof.
- No new directory, no `lakefile.toml` change, no touching `Pipeline/` or
  `DistortionConversion*.lean`.
- No strengthening `hy : ‖y‖ ≤ R` to the buffer condition "for safety" —
  if it turns out insufficient, stop and report, don't silently swap it.
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial` forbidden.
