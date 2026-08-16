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

This module is **layers 1–3, plus injectivity**, of a larger plan toward a
bounded-error statement about an *approximate* inverse — without invoking
any existence/uniqueness machinery for the *true* inverse. It proves: on a
bounded disk, the naive first-order approximate inverse (subtract the same
displacement rather than solving for it) has a composition error bounded by
`L · M · t²`; the forward map `D θ t` is injective on the disk whenever
`|t| · L θ R < 1`; and the fixed-point iteration step that a Banach
argument would use is bounded and contracting — the two prerequisites such
an argument needs, short of the argument itself. `t` is a
distortion-strength parameter, `M` bounds the displacement field, and `L`
bounds its Lipschitz constant — both explicit closed-form expressions in
the polynomial coefficients and the disk radius.

## Scope

**Status**: Layers 1–3 complete (boundedness, Lipschitz, first-order
composition-error estimate); Layer 4 prerequisites complete (injectivity,
invariant disk, contraction estimate); fixed-point existence/uniqueness
deferred.

**In scope (this module):**
- A boundedness estimate for the displacement field on a disk.
- A Lipschitz estimate for the displacement field on a disk.
- A direct algebraic (not fixed-point) bound on the first-order inverse's
  composition error.
- Injectivity of the forward map `D θ t` on the disk, under a contraction
  condition `|t| * L θ R < 1`.
- The two prerequisites (self-mapping, contraction) a future Banach
  fixed-point argument would need to additionally prove *existence* of the
  true inverse — not that existence proof itself.

**Explicitly out of scope (deferred, separate follow-on task):**
- **Layer 4's existence/uniqueness theorem itself** — the *local inversion*
  result: that `D θ t` (equivalently, the fixed point of `inverseStep θ t
  y`) actually has a true inverse on the disk, via a Banach fixed-point
  argument (Mathlib's `ContractingWith`, `CompleteSpace`, subtype/closed-
  ball API integration). The two prerequisites such an argument would need
  — `inverse_step_maps_disk`, `inverse_step_lipschitz` — are proved in this
  module; the argument itself, and the existence/uniqueness conclusion, is
  not. Injectivity (`D_eq_implies_eq`) is likewise a necessary, not
  sufficient, condition for invertibility — larger distortions
  (`|t| * L θ R ≥ 1`) may still be invertible; this module does not show
  that either way. See "Terminology" below.
- **Layer 5** — folding the `F`/mm/pixel unit-conversion machinery from
  `opencv_opentrackio_proofs/` back into this generic estimate.
- **The D-U/U-D question itself.** This module does **not** resolve
  SQ-CV-07 — it is scaffolding toward a possible future resolution, not the
  resolution. See `docs/specification-questions.md` and
  `docs/limitations.md` for the current, explicit status.

**Terminology**: `q := |t| * L θ R < 1` is a *sufficient contraction
threshold*, not shown necessary — avoid calling it an "invertibility
threshold" without qualification. What is proved is injectivity on the
disk; together with the self-map condition, `q < 1` will be a sufficient
local inversion condition for the deferred existence/uniqueness theorem,
not a demonstrated necessary one.

## Independence from `Pipeline/`

This module is deliberately separate from `opencv_opentrackio_proofs/`. The
boundedness/Lipschitz/composition-bound machinery here is generic to any
polynomial Brown-Conrady-shaped field — it does not import
`DistortionModel`, `OpenCVModel`, or any `Pipeline/*` file, and none of
those files import this one. If layers 4–5 are pursued later, they build on
this module, not on anything under `Pipeline/`.

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

`D_eq_implies_eq`/`D_injective_on_disk` establish injectivity of the
forward map. `inverse_step_maps_disk`/`inverse_step_lipschitz` establish
the self-mapping and contraction properties a Banach fixed-point argument
would need to additionally prove *existence* of the true inverse — that
existence proof is not attempted here (layer 4, deferred). Full derivation
and review: `docs/laps/inverse-injectivity/`.

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
