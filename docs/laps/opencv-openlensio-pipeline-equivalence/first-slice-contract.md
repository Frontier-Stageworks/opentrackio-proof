---
name: opencv-openlensio-pipeline-equivalence-first-slice-contract
description: Contract for SLICE-PE-00 and SLICE-PE-01 — infrastructure and undistortOpenCV definitions
metadata:
  type: project
---

# First Slice Contract — SLICE-PE-00 + SLICE-PE-01

## Scope

This contract covers:
1. **SLICE-PE-00**: `lakefile.toml` update + stub file with imports
2. **SLICE-PE-01**: Definitions of `undistortXCV`, `undistortYCV`, `undistortPointCV`

No theorem proofs in this slice. Gate: file compiles clean.

---

## lakefile.toml change (SLICE-PE-00)

Add at the end of the `opencv_opentrackio_proofs` lib block:

```toml
[[lean_lib]]
name = "PipelineEquivalence"
srcDir = "opencv_opentrackio_proofs"
```

---

## File header and imports (SLICE-PE-00)

```lean
/-
  PipelineEquivalence.lean
  
  Defines the OpenCV undistortion pipeline in normalised coordinate space and
  proves when it agrees with the OpenLensIO (OpenTrackIO) undistortion pipeline.

  Source: "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"
  SMPTE RIS, corrected 2025-09-02.

  NAMING NOTE: OpenCV uses k1,k2,k3 (numerator) and k4,k5,k6 (denominator).
  OpenLensIO uses k1,k3,k5 (numerator) and k2,k4,k6 (denominator, alternating).
  These conventions conflict. This file uses OpenCV naming for OpenCV parameters.
  When constructing RadialCoefficients (OTI type) from OpenCV params, the mapping
  is: ⟨k1, k4, k2, k5, k3, k6⟩ (OTI fields: k1,k2,k3,k4,k5,k6 → num,den,num,den,num,den).

  Theorems:
    opencv_openlensio_radial_pipeline_eq           — radial-only pipeline agreement
    opencv_openlensio_full_pipeline_pixel_sufficiency — all conversions + ws/w=fx → pixel eq
    opencv_openlensio_full_pipeline_pixel_iff       — full iff (requires p1≠0 ∨ p2≠0)
-/

import DistortionConversion
import DistortionModel
```

---

## Definitions (SLICE-PE-01)

### `undistortXCV`

```lean
/-
  undistortXCV — x-component of the OpenCV Brown-Conrady undistortion.

  Given a normalised distorted point ε and OpenCV coefficients:
    r := sensorRadius ε  (normalised radius, NOT screen-space)
    R_cv := (1 + k1·r² + k2·r⁴ + k3·r⁶) / (1 + k4·r² + k5·r⁴ + k6·r⁶)
    δx   := 2·p1·ε.x·ε.y + p2·(r² + 2·ε.x²)   (tangential in normalised space)
    output := R_cv·ε.x + δx

  Coefficient naming: k1,k2,k3 = radial numerator; k4,k5,k6 = radial denominator.
  This is the DistortionConversion.lean convention, NOT the LensSemantics.lean convention.

  hden: 1 + k4·r² + k5·r⁴ + k6·r⁶ ≠ 0 at r = sensorRadius ε.
-/
noncomputable def undistortXCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (hden : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
              + k6 * (sensorRadius ε) ^ 6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  (1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6) /
  (1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6) * ε.x
  + 2 * p1 * ε.x * ε.y + p2 * (r ^ 2 + 2 * ε.x ^ 2)
```

### `undistortYCV`

```lean
/-
  undistortYCV — y-component of the OpenCV Brown-Conrady undistortion.

  Symmetric to undistortXCV with p1/p2 roles swapped per the OpenCV tangential formula:
    δy := p1·(r² + 2·ε.y²) + 2·p2·ε.x·ε.y
-/
noncomputable def undistortYCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (hden : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
              + k6 * (sensorRadius ε) ^ 6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  (1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6) /
  (1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6) * ε.y
  + p1 * (r ^ 2 + 2 * ε.y ^ 2) + 2 * p2 * ε.x * ε.y
```

### `undistortPointCV`

```lean
/-
  undistortPointCV — full OpenCV undistortion map U : SensorPoint → SensorPoint.
  Packages undistortXCV and undistortYCV into a SensorPoint.
-/
noncomputable def undistortPointCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (hden : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
              + k6 * (sensorRadius ε) ^ 6 ≠ 0) : SensorPoint :=
  ⟨undistortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden,
   undistortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden⟩
```

---

## What is NOT in this slice

- No theorem proofs
- No radial equivalence theorem
- No iff theorem
- No `hden` derivation lemmas

---

## Compile gate

```sh
lake env lean opencv_opentrackio_proofs/PipelineEquivalence.lean
```

Expected: no output (clean).

---

## Semantic checks before declaring SLICE-PE-01 done

1. `undistortXCV` has `r = sensorRadius ε` (not an inline `sqrt`).
2. Numerator coefficients `k1, k2, k3`; denominator `k4, k5, k6`. No mix-up.
3. Tangential `δx = 2*p1*ε.x*ε.y + p2*(r^2 + 2*ε.x^2)` — matches OpenCV formula.
4. Tangential `δy = p1*(r^2 + 2*ε.y^2) + 2*p2*ε.x*ε.y` — matches OpenCV formula.
5. `undistortPointCV` assembles `⟨x_component, y_component⟩`.
6. The `hden` predicate matches the form expected by SLICE-PE-02 proofs.
