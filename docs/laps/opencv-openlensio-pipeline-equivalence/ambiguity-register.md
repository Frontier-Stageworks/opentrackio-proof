---
name: opencv-openlensio-pipeline-equivalence-ambiguity-register
description: Tracked ambiguities and design decisions for the pipeline equivalence formalization
metadata:
  type: project
---

# Ambiguity Register — OpenCV/OpenLensIO Full Pipeline Equivalence

## AMB-PE-001: Naming conflict between OTI and OpenCV radial coefficients

**Description**: The `RadialCoefficients` structure in `LensSemantics.lean` uses the
OpenLensIO convention: k1,k3,k5 = numerator; k2,k4,k6 = denominator (alternating).
`DistortionConversion.lean` uses the OpenCV convention: k1,k2,k3 = numerator;
k4,k5,k6 = denominator (sequential). These are different structures with the same
field names pointing to different physical roles.

**Risk**: Using `RadialCoefficients` to hold OpenCV coefficients would make the
denominator `1 + k2*r^2 + k4*r^4 + k6*r^6` (OTI naming) represent a different
polynomial than `1 + k4*r^2 + k5*r^4 + k6*r^6` (OpenCV naming).

**Resolution**: `undistortOpenCV` takes raw `k1 k2 k3 k4 k5 k6 : ℝ` parameters
(DistortionConversion.lean convention) directly. It does NOT use `RadialCoefficients`.
To call `radialTerm` or `denominatorNonzero` (which take `RadialCoefficients`), the
proof assembles a `RadialCoefficients` value with the mapping:
- OTI `.k1` ← CV `k1`, OTI `.k2` ← CV `k4`, OTI `.k3` ← CV `k2`
- OTI `.k4` ← CV `k5`, OTI `.k5` ← CV `k3`, OTI `.k6` ← CV `k6`
(i.e., the OTI alternating convention maps odd-indexed OTI fields to OpenCV numerator
and even-indexed OTI fields to OpenCV denominator)

**Status**: Resolved. See proof-capsule.md.

---

## AMB-PE-002: Where should `undistortOpenCV` live?

**Description**: The task says the work "lives in the opencv_opentrackio_proofs project
or a new openlensio_opencv_equivalence source file." Two options:

Option A: New file `opencv_opentrackio_proofs/PipelineEquivalence.lean`
  - Follows existing pattern (PixelEquivalence.lean, DistortionConversion.lean)
  - Simple import path: `import DistortionConversion` and `import DistortionModel`
  - No new directory

Option B: New directory `openlensio_opencv_equivalence/`
  - Cleaner separation if the equivalence work grows
  - Requires new `srcDir` in lakefile.toml

**Resolution**: Option A. The new file `opencv_opentrackio_proofs/PipelineEquivalence.lean`
stays within the existing `opencv_opentrackio_proofs` library pattern and imports
`DistortionConversion` (same dir) plus `DistortionModel` (cross-lib from openlensio_semantics).
This matches the established pattern in the project.

**Status**: Resolved.

---

## AMB-PE-003: Hypothesis `p1 ≠ 0 ∨ p2 ≠ 0` for the iff direction

**Description**: The → direction of `opencv_openlensio_full_pipeline_pixel_iff`
needs to extract `ws/w = fx` from universal pixel agreement. The extraction uses
the tangential terms: at `(x', y') = (1, 0)`, `δx_cv = 3*p2`. If `p2 = 0` and
we try `(1, 1)`, `δx_cv = 2*p1 + 3*p2 = 2*p1`. If both are zero, no tangential
contribution appears and `ws/w = fx` cannot be derived — because it is NOT
entailed by pixel agreement when `p1 = p2 = 0` (pure-radial lens).

**Options**:
1. Add hypothesis `hp2 : p2 ≠ 0` (simplest, uses (1,0) witness)
2. Add hypothesis `hp : p1 ≠ 0 ∨ p2 ≠ 0` (minimal, matches the actual condition)
3. State the iff without `ws/w = fx` on the RHS and only state the sufficiency direction

Option 2 is chosen: `hp : p1 ≠ 0 ∨ p2 ≠ 0` is the honest minimal hypothesis.
It makes the theorem non-vacuous and captures the correct domain.

**Resolution**: Use `hp : p1 ≠ 0 ∨ p2 ≠ 0` in `opencv_openlensio_full_pipeline_pixel_iff`.
The sufficiency theorem (`opencv_openlensio_full_pipeline_pixel_sufficiency`) does NOT
need this hypothesis.

**Status**: Resolved.

---

## AMB-PE-004: Does `sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'` require F > 0?

**Description**: `sensorRadius ε = Real.sqrt (ε.x^2 + ε.y^2)`.

```
sensorRadius ⟨F·x, F·y⟩ = Real.sqrt ((F·x)^2 + (F·y)^2)
                         = Real.sqrt (F^2 · (x^2 + y^2))
                         = |F| · Real.sqrt (x^2 + y^2)
                         = |F| · sensorRadius ε'
```

So `sensorRadius ⟨F·x, F·y⟩ = |F| · sensorRadius ε'`, which equals `F · sensorRadius ε'`
only when `F > 0` (so `|F| = F`).

The hypothesis `hF : F ≠ 0` is insufficient. `hF_pos : 0 < F` is needed.

**Downstream impact**: In all three theorems, wherever the OTI pipeline is evaluated at
the screen point `⟨F·ε'.x, F·ε'.y⟩`, the `hF_pos` hypothesis is required.

F > 0 is physically justified: F is the focal length in mm, always positive. The existing
`ValidLensSemantics` encodes `0 < l.focalLength`. So this is an honest hypothesis.

**Resolution**: Add `hF_pos : 0 < F` to all three theorems (in addition to `hF : F ≠ 0`).
Note: `hF_pos` implies `hF` so one could drop `hF`, but keeping both is more readable.

**Status**: Resolved. Note for implementation: use `Real.sqrt_sq_eq_abs` and `abs_of_pos`.

---

## AMB-PE-005: Inline expressions vs named helper definitions for pixel outputs

**Description**: The pixel output expressions are verbose:
```
fx * (R_cv * x' + 2*p1*x'*y' + p2*(x'^2+y'^2 + 2*x'^2)) + cx
```
vs using named helpers like `pixelOutCV fx cx k1..k6 p1 p2 x' y' hden`.

**Options**:
1. Inline (like DistortionConversion.lean's `∀ r` / `∀ x' y'` theorems)
2. Named noncomputable defs

The inline approach is consistent with the existing project style in
`PrincipalPointConversion.lean` and `DistortionConversion.lean`.
Named defs add a definitional unfolding step in proofs.

**Resolution**: Use inline expressions in the theorem statement. The definition of
`undistortXCV` is a named def (needed for SLICE-PE-01 and SLICE-PE-02). But the full
pixel output (which adds the linear projection) is spelled out inline in the main iff
theorem.

**Status**: Resolved.

---

## AMB-PE-006: Scope — 1D (x-component only) vs 2D

**Description**: The OTI pipeline has x and y components; OpenCV similarly. The paper
states the equivalence for both components simultaneously (they're symmetric).

**Options**:
1. Prove x-component only (1D); note y by symmetry
2. Prove both components

The full mathematical content is captured in 1D (the y-component is identical with
p1 ↔ p2 swapped). The project precedent (`whole_tangential_field_iff` was first 1D,
then extended to 2D) suggests 1D first.

**Resolution**: SLICE-PE-03 and SLICE-PE-04 prove the x-component. A 2D extension is
noted as future work (deferred). This is explicitly noted in the theorem file header.

**Update (2026-05-24):** The corrected OpenCV→OpenTrackIO paper (2025-09-02) explicitly
derives both the x-direction formula (F=w/w_shader·fx) AND the y-direction formula
(F=h/h_shader·fy) with ΔPy=(h/h_shader)·(cy−h_shader/2). The y-direction tangential terms
swap p₁↔p₂ relative to the x-direction, exactly as expected. The paper has already worked
out the y-direction algebra; a y-pixel Lean theorem follows the same proof structure as the
x-component with those substitutions. This is the highest near-term ROI extension — see
next-steps.md item 2A.

**Status**: Resolved — 2D extension well-grounded in the corrected paper.

---

## AMB-PE-007: OTI denominator nonzero for the screen-space denominator

**Description**: The OTI `undistortX` calls `radialTerm k_oti r_screen h_oti` where
`h_oti : denominatorNonzero k_oti r_screen`. After parameter conversion,
`denominatorNonzero k_oti r_screen` equals `1 + k4*(sensorRadius ε')^2 + ...`
(the OpenCV denominator). So `hden_oti` is derivable from `hden_cv`.

The key step: `radial_distortion_value_equivalence` already derives
`1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6 ≠ 0` from
`1 + k4*r^2 + k5*r^4 + k6*r^6 ≠ 0` when the conversion equations hold.

**Resolution**: Build `hden_oti` via `radial_distortion_value_equivalence` in each proof.
This is a `have` step, not a new theorem. See proof-plan.md.

**Status**: Resolved.
