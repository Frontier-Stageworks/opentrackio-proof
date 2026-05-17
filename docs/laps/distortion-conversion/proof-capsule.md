---
name: distortion-conversion-capsule
description: Adopted proof capsule for DistortionConversion.lean — eight distortion parameter conversion theorems
metadata:
  type: project
---

# Proof Capsule — DistortionConversion.lean

## Adoption note

This proof was written before LAPS or outside the LAPS workflow.
This capsule backfills LAPS artifacts for future maintenance.
No Lean code was changed during adoption.

## Lean check

```sh
lake env lean opencv_opentrackio_proofs/DistortionConversion.lean
```

**Result:** Clean (no output). 2026-05-16.

## Project grounding

- Lean 4 `v4.29.0`, Mathlib `v4.29.0`
- Imports: `Mathlib.Tactic` only
- No project-local imports — this file is the root of its dependency chain
- Source: SMPTE RIS paper "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters", corrected 2025-09-02

## Physical setting

OpenCV distortion uses normalised coordinates `(x', y')` with radius `r = sqrt(x'^2 + y'^2)`.
OpenTrackIO distortion uses screen coordinates `(ε_x, ε_y) = (F*x', F*y')` with radius `r_u = F*r`.

Consistency means both models apply the same correction at every normalised coordinate.

## File structure

The file is organised in two layers:

**Layer 1 — Per-term coefficient theorems** (useful as imported lemmas):
- `radial_distortion_conversion` — for any single degree-2n term, consistency → l = k/F^(2n)
- `tangential_q1_conversion` — cross-term consistency → q1 = p1/F^2
- `tangential_q2_conversion` — radial-term consistency → q2 = p2/F^2

**Layer 2 — Whole-polynomial iff theorems** (strongest statements):
- `whole_radial_polynomial_iff` — full radial numerator consistency ↔ three coefficient conversions
- `whole_tangential_field_iff` — full tangential δx consistency ↔ two coefficient conversions
- `whole_tangential_field_2d_iff` — full 2D tangential field consistency ↔ same two conversions

**Corollaries:**
- `all_distortion_conversions_iff` — full distortion model ↔ all eight parameter conversions
- `radial_coefficients_imply_rational_factor_equality` — coefficient equalities → rational factor equality (one-way)

## Theorem cluster (8 theorems)

| # | Name | Layer | Role |
|---|------|-------|------|
| 1 | `radial_distortion_conversion` | 1 | Per-term radial conversion at arbitrary degree 2n |
| 2 | `tangential_q1_conversion` | 1 | Per-term tangential cross-term conversion |
| 3 | `tangential_q2_conversion` | 1 | Per-term tangential radial-term conversion |
| 4 | `whole_radial_polynomial_iff` | 2 | Iff: full radial numerator ↔ three coefficient conversions |
| 5 | `whole_tangential_field_iff` | 2 | Iff: full tangential δx ↔ two coefficient conversions |
| 6 | `whole_tangential_field_2d_iff` | 2 | Iff: full 2D tangential field ↔ same two conversions |
| 7 | `all_distortion_conversions_iff` | corollary | Iff: full distortion model ↔ all eight conversions |
| 8 | `radial_coefficients_imply_rational_factor_equality` | corollary | One-way: coefficient equalities → rational factor equality |

## Dependency order

```
radial_distortion_conversion           ← Layer 1 root (used by MutationTests, PixelEquivalence)
tangential_q1_conversion               ← Layer 1 root (used by MutationTests)
tangential_q2_conversion               ← Layer 1 root (used by MutationTests)

whole_radial_polynomial_iff            ← Layer 2 (independent derivation within file)
  └─ all_distortion_conversions_iff

whole_tangential_field_iff             ← Layer 2
  └─ whole_tangential_field_2d_iff
       └─ all_distortion_conversions_iff

radial_coefficients_imply_rational_factor_equality  ← standalone corollary
```

Layer 1 and Layer 2 theorems are independent within this file — the whole-polynomial
theorems re-derive results by Vandermonde-style point specialisation rather than
delegating to the per-term theorems. Both derivations are correct and complementary.

## Allowed changes (for future LAPS work)

- Local `have` statements in new theorems
- New theorems (e.g. full rational factor iff, tangential y-component lemma, n=0 instance)
- Use of existing project lemmas

## Forbidden changes

- No changes to the eight existing theorem statements or hypotheses
- No weakening of conclusions
- `sorry`, `admit`, `axiom`, `unsafe`, `partial` forbidden
