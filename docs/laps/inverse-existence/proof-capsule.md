---
name: inverse-existence-capsule
description: Proof capsule for D_exists_unique_preimage — local existence and uniqueness of the true inverse of D θ t on a buffered disk, via Mathlib's Banach fixed-point theorem
metadata:
  type: project
---

# Proof Capsule — Local Existence and Uniqueness of the True Inverse

## Intent (plain English)

Direct continuation of `inverse_approximation/InverseApproximation.lean`
(same file, same module — no new directory, no new `lean_lib`). Using the
three prerequisites already proved (`inverse_step_maps_disk`,
`inverse_step_lipschitz`, `D_eq_implies_eq`), invoke Mathlib's Banach
fixed-point theorem to conclude: for every `y` in the buffer disk, there is
exactly one `z` in the disk with `D θ t z = y`. This is the theorem
`docs/laps/inverse-injectivity/` explicitly deferred (its own capsule says
"existence of the true inverse... requires Mathlib's
ContractingWith/CompleteSpace machinery... is a separate, deferred task").

This is a **standalone result about the polynomial Brown-Conrady model**.
It does not resolve `docs/specification-questions.md` SQ-CV-07 (the D-U/U-D
interoperability question) and its relevance to that question is a
separate, open matter — noted in the doc updates, not conflated with the
mathematical content of this theorem.

## Target theorem (user-specified, exact)

```lean
theorem D_exists_unique_preimage
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y : ℂ) (hy : ‖y‖ + |t| * M θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y
```

## Feasibility check (done before committing to this plan)

The user's prompt set an explicit hard time-box: stop after ~2-3 iterations
of Mathlib subtype/API friction and report a documented stopping point
rather than push through. Given the risk, the entire existence+uniqueness
architecture was validated **in an isolated scratch file first**, using
placeholder hypotheses shaped exactly like `inverse_step_maps_disk`/
`inverse_step_lipschitz` (not yet touching the real file), before writing
this capsule. Result: compiles end-to-end, needing only one minor
direction-mismatch fix (`w = z` vs `z = w` in the final `exact`). Full
scratch code preserved in `proof-plan.md` below. This capsule is written
with that confirmed feasibility in hand, not as a speculative plan.

## Load-bearing Mathlib API (confirmed names, this exact Mathlib version)

| Name | Role |
|---|---|
| `Metric.isClosed_closedBall` | disk is closed |
| `IsClosed.isComplete` | closed subset of a complete space is complete |
| `ContractingWith.exists_fixedPoint'` | Banach theorem for a contracting self-map on a complete *set* (not a bundled subtype) — avoids most subtype friction |
| `LipschitzWith.of_dist_le_mul` | build `LipschitzWith K f` from a `dist`-based bound |
| `MapsTo.restrict` | restriction of `f` to `s → s`, used internally by `exists_fixedPoint'`'s `ContractingWith` hypothesis |
| `Real.coe_toNNReal` | convert the real contraction constant to `ℝ≥0` |
| `ContractingWith.fixedPoint_unique'` | uniqueness of fixed points of a `ContractingWith` map, used to finish the `∃!` uniqueness clause |
| `Subtype.dist_eq` | `dist` on a subtype equals `dist` of the coerced values (used inside the `LipschitzWith` proof for the restricted map) |

## Existing load-bearing theorems reused (read-only)

| Name | Role |
|---|---|
| `inverse_step_maps_disk` | supplies `MapsTo (inverseStep θ t y) s s` |
| `inverse_step_lipschitz` | supplies the `dist`-based bound feeding `LipschitzWith.of_dist_le_mul` |
| `D_eq_implies_eq` | NOT needed in the final proof architecture (uniqueness comes directly from `ContractingWith.fixedPoint_unique'`); kept available as a cross-check per the user's "whichever is cleaner" — see ambiguity-register.md |
| `inverseStep`, `D`, `M`, `L`, `Φ` | definitions, unfolded for the final `D θ t z = y ↔ inverseStep θ t y z = z` translation |

## Allowed changes

- Append `D_exists_unique_preimage` to `InverseApproximation.lean`.
- Small local `have`s inside its proof.
- If it completes cleanly: update the header comment in
  `InverseApproximation.lean` and `inverse_approximation/README.md` to
  reflect that local existence/uniqueness is now proved (not just the
  prerequisites), and add a note to `docs/specification-questions.md`
  SQ-CV-07 per the user's exact instruction.

## Forbidden changes

- No edit to any existing declaration in `InverseApproximation.lean`.
- No new directory, no `lakefile.toml` change.
- No weakening of the target theorem statement, no unjustified extra
  hypotheses, no `sorry` to force a "success" report.
- If the hard time-box is hit: do not keep iterating past it. Stop, record
  precisely where in `proof-review.md`, report the documented stopping
  point. (Not expected to trigger, given the pre-validated scratch test,
  but the rule stands regardless.)
