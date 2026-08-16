# Bounded Inverse Approximation

This directory contains a machine-checked, generic (non-OpenCV-specific)
bounded-error estimate for a first-order approximate inverse of a polynomial
Brown-Conrady-shaped displacement field, on a bounded disk.

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

This module is **layers 1–3** of a larger plan toward a bounded-error
statement about an *approximate* inverse — without invoking any
existence/uniqueness machinery for the *true* inverse. It proves: on a
bounded disk, the naive first-order approximate inverse (subtract the same
displacement rather than solving for it) has a composition error bounded by
`L · M · t²`, where `t` is a distortion-strength parameter, `M` bounds the
displacement field, and `L` bounds its Lipschitz constant — both explicit
closed-form expressions in the polynomial coefficients and the disk radius.

## Scope

**In scope (this module):**
- A boundedness estimate for the displacement field on a disk.
- A Lipschitz estimate for the displacement field on a disk.
- A direct algebraic (not fixed-point) bound on the first-order inverse's
  composition error.

**Explicitly out of scope (deferred, separate follow-on tasks):**
- **Layer 4** — existence/uniqueness of the *true* inverse of the scaled
  distortion map via a fixed-point/contraction argument (would use
  Mathlib's Banach fixed-point machinery; none of that is used here).
- **Layer 5** — folding the `F`/mm/pixel unit-conversion machinery from
  `opencv_opentrackio_proofs/` back into this generic estimate.
- **The D-U/U-D question itself.** This module does **not** resolve
  SQ-CV-07 — it is scaffolding toward a possible future resolution, not the
  resolution. See `docs/specification-questions.md` and
  `docs/limitations.md` for the current, explicit status.

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

## Files

| File | Contents |
|------|----------|
| `InverseApproximation.lean` | `Coeffs`, `Φ`, `D`, `U`, `M`, `L` definitions; `phi_bounded`, `phi_lipschitz`, `inverse_approx_error` theorems |

## Dependencies

- Lean 4 v4.29.0, Mathlib v4.29.0
- No dependency on `opencv_opentrackio_proofs/` or `openlensio_semantics/`

## LAPS artifacts

Full proof capsule, statement audit, ambiguity register, proof plan, algebra
plan, run log, and review are in
`docs/laps/bounded-inverse-approximation/`.
