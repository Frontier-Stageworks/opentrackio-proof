---
name: principal-point-conversion-capsule
description: Adopted proof capsule for PrincipalPointConversion.lean — five principal-point and focal-length theorems
metadata:
  type: project
---

# Proof Capsule — PrincipalPointConversion.lean

## Adoption note

This proof was written before LAPS or outside the LAPS workflow.
This capsule backfills LAPS artifacts for future maintenance.
No Lean code was changed during adoption.

## Lean check

```sh
lake env lean opencv_opentrackio_proofs/PrincipalPointConversion.lean
```

**Result:** Clean (no output). 2026-05-16.

## Project grounding

- Lean 4 `v4.29.0`, Mathlib `v4.29.0`
- Imports: `Mathlib.Tactic` only
- No project-local imports — this file is the root of the dependency graph
- Source: SMPTE RIS paper "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters", corrected 2025-09-02

## Physical setting

OpenCV pixel space: `u = fx * x'' + cx` (upper-left origin).
OpenTrackIO screen space: `u = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2` (centre origin).
Consistency means both assign the same pixel `u` to every normalised coordinate `x''`.

## Theorem cluster (5 theorems)

| # | Name | Role |
|---|------|------|
| 1 | `principal_point_conversion_necessary` | Derives the unique F and ΔPx from consistency (necessity half) |
| 2 | `principal_point_conversion_iff` | Iff: consistency ↔ correct formulas (1D) |
| 3 | `principal_point_conversion_2d_iff` | Iff: 2D consistency ↔ correct formulas for both axes |
| 4 | `single_focal_length_compatibility` | If 2D consistent, both axes determine the same F |
| 5 | `buggy_principal_point_conversion_inconsistent` | The old buggy formula (missing centering) is inconsistent |

## Dependency order

```
principal_point_conversion_necessary
  ├─ principal_point_conversion_iff
  │    └─ principal_point_conversion_2d_iff
  │         └─ single_focal_length_compatibility
  └─ buggy_principal_point_conversion_inconsistent
```

Theorem 1 is the load-bearing lemma. All other theorems in this file and in
`PixelEquivalence.lean` and `MutationTests.lean` ultimately depend on it.

## Allowed changes (for future LAPS work)

- Local `have` statements in new theorems
- New theorems (e.g. extensions to non-square sensors, alternative parameterizations)
- Use of existing project lemmas

## Forbidden changes

- No changes to the five existing theorem statements or hypotheses
- No weakening of conclusions
- `sorry`, `admit`, `axiom`, `unsafe`, `partial` forbidden
