# Bounded Inverse Approximation

A machine-checked quantitative first-order inverse approximation theorem
for the full polynomial radial+tangential Brown–Conrady displacement field
on a bounded disk. Generic and non-OpenCV-specific.

## Background and motivation

`docs/specification-questions.md` SQ-CV-07 raises an open question: the
pipeline theorems in `opencv_opentrackio_proofs/Pipeline/` prove a
same-direction (undistorted→distorted, "U→D") coordinate-conjugacy between
OpenCV's forward-distortion formula and OpenTrackIO's converted
coefficients — they do **not** establish anything about OpenTrackIO's
*native* undistortion consumption of those coefficients (the opposite,
"D→U" direction, which is the OpenTrackIO JSON schema's default for
`distortion.model`). Answering that D→U question rigorously requires
knowing something about the actual *inverse* of the distortion map, which
has no closed form for the general Brown-Conrady model
(`docs/limitations.md`, SQ-OL-03).

This module is **layers 1–4 complete**: a bounded-error statement about an
*approximate* inverse, and a genuine local existence/uniqueness theorem for
the *true* inverse, both on a bounded disk. It proves: the naive
first-order approximate inverse (subtract the same displacement rather
than solving for it) has a composition error bounded by `L · M · t²`; the
forward map `D θ t` is injective on the disk whenever `|t| · L θ R < 1`;
the fixed-point iteration step that a Banach argument uses is bounded and
contracting; and — via Mathlib's Banach fixed-point theorem — for every `y`
in a buffer disk there is exactly one `z` in the disk with `D θ t z = y`.
`t` is a distortion-strength parameter, `M` bounds the displacement field,
and `L` bounds its Lipschitz constant — both explicit closed-form
expressions in the polynomial coefficients and the disk radius.

## Scope

**Status**: Layers 1–4 complete — boundedness, Lipschitz, first-order
composition-error estimate, injectivity, invariant disk, contraction
estimate, and (via Mathlib's Banach fixed-point theorem) local existence
and uniqueness of the true inverse (`D_exists_unique_preimage`). Since
then, `inverse_approx_error_vs_preimage`/`inverse_approx_exists_unique_with_error`
connect the two: the one-step approximation's error is now bounded
relative to the *true* preimage (not just the round-trip residual
`inverse_approx_error` already bounded), with the error-bound proof itself
kept independent of the existence machinery — only the packaging corollary
depends on it.

**In scope (this module):**
- A boundedness estimate for the displacement field on a disk.
- A Lipschitz estimate for the displacement field on a disk.
- A direct algebraic (not fixed-point) bound on the first-order inverse's
  composition error.
- Injectivity of the forward map `D θ t` on the disk, under a contraction
  condition `|t| * L θ R < 1`.
- The self-mapping and contraction properties of the fixed-point iteration
  step `inverseStep θ t y`.
- **Local existence and uniqueness of the true inverse of `D θ t` on a
  buffer disk**, via Mathlib's Banach fixed-point theorem
  (`ContractingWith.exists_fixedPoint'`) applied to `inverseStep θ t y`.

**Explicitly out of scope (separate follow-on tasks):**
- **Layer 5** — folding the `F`/mm/pixel unit-conversion machinery from
  `opencv_opentrackio_proofs/` back into this generic estimate.
- **The D-U/U-D question itself.** This module does **not** resolve
  SQ-CV-07 — proving that the polynomial model has a true local inverse on
  some rigorous domain is a standalone mathematical fact, not an answer to
  which direction real OpenTrackIO producers/consumers should compute.
  Its relevance to that interoperability question is a separate, open
  matter. See `docs/specification-questions.md` and `docs/limitations.md`
  for the current, explicit status.

**Terminology**: `q := |t| * L θ R < 1` is a *sufficient contraction
threshold*, not shown necessary — avoid calling it an "invertibility
threshold" without qualification. `D_exists_unique_preimage` shows `q < 1`
(together with the buffer/self-map condition) IS sufficient for local
existence and uniqueness — that part is no longer merely anticipated, it's
proved. What remains unshown is necessity: larger distortions
(`|t| * L θ R ≥ 1`) may still be invertible; this module does not
characterize that boundary either way.

## Independence from `Pipeline/`

This module is deliberately separate from `opencv_opentrackio_proofs/`. The
boundedness/Lipschitz/composition-bound machinery here is generic to any
polynomial Brown-Conrady-shaped field — it does not import
`DistortionModel`, `OpenCVModel`, or any `Pipeline/*` file, and none of
those files import this one. Layer 4 was built directly on this module,
not on anything under `Pipeline/`; if layer 5 is pursued later, the same
applies.

## Vector-space representation

Uses `ℂ` (not a bespoke `SensorPoint`-style struct, not
`EuclideanSpace ℝ (Fin 2)`) — chosen specifically to inherit Mathlib's
`NormedField ℂ` triangle-inequality/scalar-norm API directly, avoiding
hand-proving those from scratch for a bespoke 2D type. See
`docs/laps/bounded-inverse-approximation/ambiguity-register.md` (AMB-BIA-001)
for the full reasoning and the alternatives considered.

## Theorems

All in the single file `InverseApproximation.lean`.

| Theorem | Statement |
|---|---|
| `phi_bounded` | `‖Φ θ z‖ ≤ M θ R` for `‖z‖ ≤ R` |
| `phi_lipschitz` | `‖Φ θ a - Φ θ b‖ ≤ L θ R · ‖a - b‖` for `‖a‖, ‖b‖ ≤ R` |
| `inverse_approx_error` | `‖U θ t (D θ t x) - x‖ ≤ L θ R · M θ R · t²` — the first-order approximate inverse's composition error, on a buffer disk |
| `D_eq_implies_eq` | `D θ t` is injective on the disk: `D θ t a = D θ t b → a = b`, given the contraction condition `\|t\| · L θ R < 1` |
| `D_injective_on_disk` | `Set.InjOn (D θ t) {z : ℂ \| ‖z‖ ≤ R}` — thin corollary of `D_eq_implies_eq` |
| `inverse_step_maps_disk` | the fixed-point iteration step `inverseStep θ t y z = y - t • Φ θ z` maps the disk into itself, given the same buffer condition as `inverse_approx_error` |
| `inverse_step_lipschitz` | `inverseStep θ t y` is itself a contraction on the disk, with constant `\|t\| · L θ R` — the same quantity `D_eq_implies_eq`'s `hcontract` uses |
| `D_exists_unique_preimage` | `∃! z, ‖z‖ ≤ R ∧ D θ t z = y` for `y` in a buffer disk — **local existence and uniqueness of the true inverse** of `D θ t`, via Mathlib's Banach fixed-point theorem applied to `inverseStep θ t y` |
| `inverse_approx_error_vs_preimage` | `‖U θ t y - z‖ ≤ (\|t\|²·L θ R·M θ R)/(1-\|t\|·L θ R)` given a genuine preimage `z` (`D θ t z = y`) — bounds the one-step approximation's error relative to the *true* preimage, not just the round-trip residual. Self-contained: no Banach/existence machinery, `‖y‖≤R` only (not the buffer condition) |
| `inverse_approx_exists_unique_with_error` | `∃! z, ‖z‖≤R ∧ D θ t z = y ∧ ‖U θ t y - z‖ ≤ (...)` — thin corollary attaching `inverse_approx_error_vs_preimage`'s bound to the `z` given by `D_exists_unique_preimage` |

`D_eq_implies_eq`/`D_injective_on_disk` establish injectivity of the
forward map. `inverse_step_maps_disk`/`inverse_step_lipschitz` establish
the self-mapping and contraction properties a Banach fixed-point argument
needs. `D_exists_unique_preimage` completes the argument: existence and
uniqueness of the true inverse, not just its prerequisites.
`inverse_approx_error_vs_preimage` then answers a question none of the
above do: *given* a true preimage `z`, how close is the cheap,
non-iterative `U θ t y` to it? — deliberately independent of the existence
proof (no `ContractingWith`/`CompleteSpace` anywhere in its proof);
`inverse_approx_exists_unique_with_error` is the only place that
dependency is introduced, to package both facts about the same `z`
together. Full derivation and review: `docs/laps/inverse-injectivity/`
(injectivity, prerequisites), `docs/laps/inverse-existence/`
(existence/uniqueness), and `docs/laps/inverse-approx-error/`
(error-vs-preimage bound).

**Helper lemmas** (internal building blocks, not the main results):
`radial_bounded`, `radial_lipschitz`, `normSq_lipschitz`,
`normSq_sq_lipschitz`, `normSq_cube_lipschitz` (boundedness/Lipschitz for
the radial factor alone) and `smul_norm` (`‖t • w‖ = \|t\| · ‖w‖`, reused
across several of the theorems above).

## Dependencies

- Lean 4 v4.29.0, Mathlib v4.29.0
- No dependency on `opencv_opentrackio_proofs/` or `openlensio_semantics/`

## LAPS artifacts

- `docs/laps/bounded-inverse-approximation/` — `Φ`, `D`, `U`, `M`, `L`,
  `phi_bounded`, `phi_lipschitz`, `inverse_approx_error` (proof capsule,
  statement audit, ambiguity register, proof plan, algebra plan, run log,
  review).
- `docs/laps/inverse-injectivity/` — `smul_norm`, `D_eq_implies_eq`,
  `D_injective_on_disk`, `inverseStep`, `inverse_step_maps_disk`,
  `inverse_step_lipschitz` (same artifact structure).
- `docs/laps/inverse-approx-error/` — `inverse_approx_error_vs_preimage`,
  `inverse_approx_exists_unique_with_error` (same artifact structure;
  includes the by-hand derivation and a scratch-tested division step).
- `docs/laps/inverse-existence/` — `D_exists_unique_preimage` (same
  artifact structure; includes a pre-validated scratch architecture for the
  Mathlib fixed-point/completeness API integration).
