---
name: opencv-openlensio-pipeline-equivalence-capsule
description: Proof capsule for full OpenCV/OpenLensIO pipeline equivalence — undistortOpenCV definition + three theorems establishing when the two pipelines agree
metadata:
  type: project
---

# Proof Capsule — OpenCV/OpenLensIO Full Pipeline Equivalence

## Intent (plain English)

The existing proofs in `DistortionConversion.lean` and `PixelEquivalence.lean` formalize
the *parameter conversion formulas* (k→l, p→q, cx→ΔP) and prove they are necessary and
sufficient for coefficient-level agreement. They do not yet formalize what each pipeline
*computes* at a given image point, so they cannot answer the question: "after parameter
conversion, do the two pipelines produce the same pixel output?"

This work closes that gap by:

1. **Defining `undistortOpenCV`** — the OpenCV Brown-Conrady pipeline as a concrete
   Lean function in normalised coordinate space (tangential terms evaluated at the
   normalised radius r, not the screen-space radius r_u = F·r).

2. **Proving `opencv_openlensio_radial_pipeline_eq`** — the radial-only pipelines agree
   at corresponding points after parameter conversion. This follows quickly from
   `radial_distortion_value_equivalence`.

3. **Proving `opencv_openlensio_full_pipeline_pixel_iff`** — the full (radial + tangential
   + linear projection) pixel outputs agree for ALL normalised input points if and only
   if all parameter conversions hold AND `ws/w = fx`.

The third theorem turns the paper's central claim — "coefficient equality does not imply
semantic equivalence" — into a proved theorem with explicit, minimal conditions.

## Lean grounding

- Lean 4 `v4.29.0`, Mathlib `v4.29.0`
- New source file: `opencv_opentrackio_proofs/PipelineEquivalence.lean`
- Imports: `DistortionConversion`, `DistortionModel` (from `openlensio_semantics`)
- New `lean_lib` entry required in `lakefile.toml`

## Existing load-bearing definitions (must not change)

| Name | File | Role |
|------|------|------|
| `undistortX`, `undistortY`, `undistortPoint` | `DistortionModel.lean` | OTI Brown-Conrady pipeline |
| `denominatorNonzero` | `RadialPolynomial.lean` | OTI denominator predicate |
| `radialTerm` | `RadialPolynomial.lean` | OTI rational radial factor |
| `SensorPoint`, `sensorRadius` | `CoordinateTypes.lean` | Coordinate type and radius |
| `RadialCoefficients` (k1,k3,k5=num; k2,k4,k6=den) | `LensSemantics.lean` | OTI coefficient naming |
| `radial_distortion_value_equivalence` | `PixelEquivalence.lean` | Radial scale agreement |
| `linear_projection_pixel_equivalence_2d_iff` | `PixelEquivalence.lean` | Linear projection iff |
| `all_distortion_conversions_iff` | `DistortionConversion.lean` | Coefficient iff cluster |

## New definitions to create

| Name | File | Type |
|------|------|------|
| `undistortXCV` | `PipelineEquivalence.lean` | Normalised-space x-component of OpenCV undistortion |
| `undistortYCV` | `PipelineEquivalence.lean` | Normalised-space y-component |
| `undistortPointCV` | `PipelineEquivalence.lean` | Full OpenCV undistortion map |

Design choice: `undistortPointCV` takes a `SensorPoint` (reused from OTI) for normalised
coordinates, and uses raw `ℝ` parameters with DistortionConversion.lean naming
(k1–k3=numerator, k4–k6=denominator, p1, p2). It does NOT use `RadialCoefficients` to
avoid the naming-conflict ambiguity (OTI has k1,k3,k5=num; OpenCV has k1,k2,k3=num).

## Theorem texts (specification-level)

### Theorem 1: Radial pipeline equivalence

```lean
theorem opencv_openlensio_radial_pipeline_eq
    (k1 k2 k3 k4 k5 k6 : ℝ)    -- OpenCV radial (k1-3=num, k4-6=den)
    (l1 l3 l5 l2 l4 l6 : ℝ)    -- OTI radial (OpenLensIO naming: l1,l3,l5=num; l2,l4,l6=den)
    (F : ℝ) (hF : F ≠ 0) (ε' : SensorPoint)
    (hl1 : l1 = k1/F^2) (hl3 : l3 = k2/F^4) (hl5 : l5 = k3/F^6)
    (hl2 : l2 = k4/F^2) (hl4 : l4 = k5/F^4) (hl6 : l6 = k6/F^6)
    (hF_pos : 0 < F)   -- needed to relate sensorRadius of screen vs normalised point
    (hden_cv : <OpenCV denominator nonzero at sensorRadius ε'>) :
    -- The radial scale at normalised radius r equals the OTI radial scale at F*r
    -- i.e., undistortPointCV with p1=p2=0 equals (1/F)·undistortPointOTI at (F·ε')
    ...
```

(Precise statement refined in statement-audit.md and first-slice-contract.md.)

### Theorem 2: Full pipeline pixel sufficiency (← direction)

```lean
theorem opencv_openlensio_full_pipeline_pixel_sufficiency
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l3 l5 l2 l4 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0)
    (hden : ∀ x' y' : ℝ, 1 + k4*(x'^2+y'^2) + k5*(x'^2+y'^2)^2 + k6*(x'^2+y'^2)^3 ≠ 0)
    -- All parameter conversions
    (hl1 : l1 = k1/F^2) ... (hq1 : q1 = p1/F^2) (hq2 : q2 = p2/F^2)
    (hF_eq : F = (w/ws)*fx) (hΔPx : ΔPx = (w/ws)*(cx - ws/2))
    -- The critical extra condition
    (hscale : ws/w = fx) :
    ∀ x' y' : ℝ, pixelOutCV ... x' y' = pixelOutOTI ... x' y'
```

### Theorem 3: Full pipeline pixel iff (main result)

The iff form of the above, with the → direction extracting all conditions from
universal pixel agreement (requires tangential coefficients not both zero for
the `ws/w = fx` extraction).

```lean
theorem opencv_openlensio_full_pipeline_pixel_iff
    ...
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)   -- needed for → direction's ws/w = fx extraction
    :
    (∀ x' y', pixelOutCV x' y' = pixelOutOTI x' y') ↔
    (l1 = k1/F^2 ∧ ... ∧ q1 = p1/F^2 ∧ q2 = p2/F^2 ∧
     F = (w/ws)*fx ∧ ΔPx = (w/ws)*(cx - ws/2) ∧ ws/w = fx)
```

See ambiguity-register.md item AMB-PE-003 for discussion of `p1 ≠ 0 ∨ p2 ≠ 0`.

## The key mathematical fact (informal)

After parameter conversion and `F = (w/ws)·fx`:

```
OTI pixel output  = fx·R_cv·x' + (ws/w)·δx_cv + cx
OpenCV pixel output = fx·R_cv·x' + fx·δx_cv + cx
```

Difference: `(ws/w - fx)·δx_cv`. Zero for all (x', y') iff `ws/w = fx` (when not all
tangential terms vanish).

The radial parts agree automatically after conversion (no extra condition needed).
The tangential parts differ by a scale factor — this is the semantic content of the
paper's central claim.

## Allowed changes

- New definitions `undistortXCV`, `undistortYCV`, `undistortPointCV`
- New theorems as listed above
- Local `have` statements and helper lemmas inside proofs
- `lakefile.toml`: add `PipelineEquivalence` lib entry
- Statement refinement of theorems 1–3, authorized per first-slice-contract.md

## Forbidden changes

- No changes to existing theorem statements in any file
- No changes to existing load-bearing definitions
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial` forbidden
- Do not conflate OTI RadialCoefficients naming (k1,k3,k5=num) with OpenCV naming (k1,k2,k3=num)
