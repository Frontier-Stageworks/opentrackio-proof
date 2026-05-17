---
name: pixel-equivalence-capsule
description: Adopted proof capsule for PixelEquivalence.lean — two semantic preservation theorems
metadata:
  type: project
---

# Proof Capsule — PixelEquivalence.lean

## Adoption note

This proof was written before LAPS or outside the LAPS workflow.
This capsule backfills LAPS artifacts for future maintenance.
No Lean code was changed during adoption.

## Lean check

```sh
lake env lean opencv_opentrackio_proofs/PixelEquivalence.lean
```

**Result:** Clean (no output). 2026-05-16.

## Project grounding

- Lean 4 `v4.29.0`, Mathlib `v4.29.0`
- Imports: `Mathlib.Tactic`, `PrincipalPointConversion`
- No import of `DistortionConversion` — theorems in this file do not use the polynomial iff theorems; they take coefficient equations directly as hypotheses
- Source: SMPTE RIS paper "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters", corrected 2025-09-02

## Theorem cluster

Two semantic preservation theorems:

1. **`linear_projection_pixel_equivalence_2d_iff`** — The 2D pinhole projection agrees in both camera models for all input points iff the published conversion formulas hold. A direct restatement of `principal_point_conversion_2d_iff`.

2. **`radial_distortion_value_equivalence`** — Under the published coefficient conversions, the rational radial scale factor has the same value in both models. Also derives OTI denominator nonzero-ness from OpenCV denominator nonzero-ness.

## Explicit scope limitation (documented in file header)

Full end-to-end pipeline composition (linear + distortion + tangential) is left as future work. The reason is documented: OpenCV tangential terms operate in normalised space; OpenTrackIO tangential terms in screen space. After parameter conversion, the tangential pixel contribution scales by `(ws/w)·pi` not `fx·pi`, and these are equal only when `ws/w = fx`, which is not generally true. The paper does not fully fix the composition semantics.

This limitation is intentional and honestly documented — it is not a proof gap.

## Allowed changes (for future LAPS work)

- Local `have` statements in new theorems
- New theorem additions (e.g., tangential value equivalence if the paper fixes composition semantics)
- Use of existing project lemmas

## Forbidden changes

- No theorem weakening
- No changes to the two existing theorem statements or hypotheses
- `sorry`, `admit`, `axiom`, `unsafe`, `partial` forbidden
