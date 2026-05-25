# openlensio_semantics — Lens Model Semantics

Lean 4 formal verification of the [OpenLensIO](https://openlensio.org) v1.0.1
Brown-Conrady distortion pipeline (D→U undistortion direction). 21 public theorems
across 12 source files, all proved over exact reals (ℝ) using Mathlib's noncomputable
infrastructure.

---

## Why this exists

Parser correctness is not semantic correctness. Two implementations can decode
identical byte sequences to identical numeric values and still render different images
if their coordinate systems, offsets, or composition orders differ.

The OpenLensIO and OpenCV lens models both use Brown-Conrady tangential distortion with
coefficients named p1 and p2. Their formulas look similar but differ in coordinate
frame: OpenLensIO evaluates undistortion in the distortion-center frame (shifted by
ΔC + ΔP), while OpenCV evaluates tangential terms in normalised space. A camera tracker
that exports OpenLensIO coefficients interpreted as OpenCV coefficients will produce
incorrect renders even when both sides implement their own specifications exactly.

This library formalizes what OpenLensIO v1.0.1 specifies the pipeline to compute.

---

## What is proved

### Model identity under zero coefficients

```lean
theorem brown_conrady_zero_identity
theorem tangential_zero_coefficients_identity
theorem radial_zero_coefficients_identity
```

All-zero radial and tangential coefficients reduce undistortion to the identity map.
`radial_denominator_nonzero_zero_coeffs` proves that zero denominator coefficients
make the denominator identically 1, confirming the domain predicate is satisfiable.

### Coordinate offset characterizations

```lean
theorem deltaP_characterisation
theorem deltaC_characterisation
theorem distortion_center_translation_commutes
```

These pin down the sign conventions for ΔP (perspective offset) and ΔC (distortion
center). `distortion_center_translation_commutes` is the load-bearing lemma for the
FOV ↔ projection consistency result: the ΔP terms cancel when substituting
`ε_d = ε'_d + ΔP` (Eq 13), so both characterizations apply undistortion U to the
same distortion-centered argument `ε'_d − ΔC`.

### Pipeline structural consistency

```lean
theorem fov_undistort_eq
theorem projection_matrix_undistort_eq
```

The FOV form (Eq 10) and the projection-matrix form (Eq 4) of undistortion are
structurally consistent: given `ε_d = ε'_d + ΔP`, undistorting `ε'_d + ΔP` in the
projection form equals undistorting `ε'_d` in the FOV form plus ΔP. The proof
requires a congruence lemma bridging the two forms' differently-typed domain
evidence for the same mathematical condition.

### Coordinate space conversions

```lean
theorem pixel_metric_roundtrip
theorem image_texture_coordinate_roundtrip
```

Metric-to-shader and shader-to-metric conversions are mutual inverses under sensor
positivity conditions (`ws > 0`, `hs > 0`, shader width `> 0`).

### Angle of view

```lean
theorem angle_of_view_eq
```

Confirms the trigonometric relationship `tan(α/2) = r_u / F`, connecting the formal
definition to the specification's Eq (18).

### Semantic extraction soundness

```lean
theorem semanticExtraction_sound
```

Lens parameter extraction from the raw `LensSemantics` record satisfies
`ValidLensSemantics` — in particular, `0 < focalLength`.

### Invertibility and injectivity

```lean
theorem undistortPoint_injective_zero_tangential
theorem undistortPoint_injective_pure_radial
theorem undistortPoint_injective_on_circle_tangential
theorem radialTerm_pos
theorem radialTerm_ne_zero
lemma radialTerm_eq_radialScale
theorem radialDescale_left_inverse_zero_tangential
```

Injectivity of `undistortPoint` is proved in three stages for progressively richer
coefficient regimes. All results require a per-point `denominatorNonzero` domain predicate.

`undistortPoint_injective_zero_tangential` (on-circle, p=0): if two points share the same
sensor radius and U maps them to the same output with R ≠ 0, they are equal. Proved by
`mul_left_cancel₀` after tangential terms simplify to zero.

`undistortPoint_injective_pure_radial` (global, p=0): extends the on-circle result to all of
ℝ² given a caller-supplied hypothesis that r ↦ R(r)·r is injective on nonneg reals. Squares
both component equalities, adds them, uses `Real.sq_sqrt` to relate `sensorRadius²` to
`ε.x² + ε.y²`, then reduces to the on-circle result via `nlinarith`.

`undistortPoint_injective_on_circle_tangential` (on-circle, full p): holds on a fixed-radius
circle given `hDet ≠ 0`, where `hDet` is the determinant of the 2×2 linear system in δx, δy
obtained by subtracting the U-equal component equations. Proved by `linear_combination` with
determinant cofactors, then `mul_eq_zero` to conclude.

`radialTerm_pos` / `radialTerm_ne_zero`: R(r) > 0 and R(r) ≠ 0 follow from per-point
polynomial positivity hypotheses on the numerator and denominator. No global coefficient
constraints are needed; `div_pos` closes the goal.

`radialDescale_left_inverse_zero_tangential`: D(r, ε) = ⟨ε.x/R(r), ε.y/R(r)⟩
satisfies D(r, U(ε)) = ε when p = 0 and R(r) ≠ 0. This is a *conditional* left
inverse, not a local inverse in the standard sense. A local inverse of U at ε₀ would
be a function of the output alone — g(U(ε)) = ε — with no extra input information. But
`radialDescale` takes r = sensorRadius(ε) as an explicit parameter, meaning the caller
must already know the input radius to recover the input. Determining r from U(ε) alone
requires inverting the map r ↦ R(r)·r, which the OpenLensIO spec (Eq 11) says requires
numerical iteration for the general model. The explicit r parameter is the formal record
of this gap.

---

## Key definitions

| Name | File | Role |
|------|------|------|
| `SensorPoint`, `sensorRadius` | `CoordinateTypes.lean` | 2D coordinate type and radius |
| `RadialCoefficients` | `LensSemantics.lean` | k1–k6 in alternating num/den form (k1,k3,k5=num; k2,k4,k6=den) |
| `TangentialCoefficients` | `LensSemantics.lean` | p1, p2 coefficients |
| `LensSemantics`, `ValidLensSemantics` | `LensSemantics.lean` | Lens record with `0 < focalLength` predicate |
| `denominatorNonzero` | `RadialPolynomial.lean` | Per-point domain predicate — callers must supply |
| `radialTerm` | `RadialPolynomial.lean` | Rational radial scale factor |
| `radialScale` | `InjectivityModel.lean` | Factored form of `radialTerm` without domain proof — used as the injectivity argument's scale function |
| `radialDescale` | `InjectivityModel.lean` | Concrete left inverse of `undistortPoint` for p=0: ⟨ε.x/R(r), ε.y/R(r)⟩ with explicit radius parameter |
| `undistortPoint` | `DistortionModel.lean` | Full Brown-Conrady undistortion |
| `undistortFromDistorted` | `ProjectionModel.lean` | Projection-matrix form (Eq 4) |
| `fovUndistortFromDistorted` | `FovModel.lean` | FOV form (Eq 10) |
| `undistortPoint_float` | `ExecutableSemanticOracle.lean` | IEEE 754 approximation — **not formally proved** |

**Coefficient naming note.** `RadialCoefficients` uses the OpenLensIO alternating
convention: k1, k3, k5 = numerator; k2, k4, k6 = denominator. This differs from
OpenCV's sequential convention (k1, k2, k3 = numerator; k4, k5, k6 = denominator).
The `opencv_opentrackio_proofs` conversion library maps between the two; do not
conflate them.

---

## Executable layer

`ExecutableSemanticOracle.lean` provides `undistortPoint_float`,
`undistortFromDistorted_float`, and related functions as IEEE 754
double-precision computations. These are **not formally proved** — they bridge
to the exact-real layer for differential testing only. No theorem connects Float
behavior to the exact-real definitions; error-bound machinery is outside scope.

A Python reference implementation (`battery-tester/semantic_oracle/reference_oracle.py`)
independently implements every formula and is validated against the same fixture suite
of seven hand-computed cases.

---

## What is not proved

| Limitation | Notes |
|---|---|
| Local inverse of U | Not proved. A local inverse g would satisfy g(U(ε)) = ε using only the output — no extra input information. `radialDescale` is a conditional left inverse that requires the input radius r as an explicit parameter; it does not constitute a local inverse. Proving a local inverse would require either a formula that recovers r from U(ε) alone, or an IFT-style argument that the Jacobian of U is nonzero (not in scope). |
| Closed-form forward distortion D (general case) | No closed-form D = U⁻¹ exists for general Brown-Conrady. The spec (Eq 11) prescribes numerical iteration. For p=0, `radialDescale_left_inverse_zero_tangential` proves D(r, U(ε)) = ε given the input radius r as an extra parameter — a conditional result, not a full inverse. |
| Global injectivity with full tangential | Proved on fixed-radius circles given a nonzero-determinant hypothesis (`hDet`). Whether `hDet ≠ 0` holds globally for all coefficient tuples is outside the algebraic scope of this library. |
| Injectivity of r ↦ R(r)·r (pure-radial case) | `undistortPoint_injective_pure_radial` accepts this as a caller-supplied hypothesis (`hScaleInj`). Proving it from coefficient bounds requires monotone-function machinery not yet in scope. |
| General invertibility and continuity | Plausible for well-calibrated lenses but outside the algebraic scope of this library. |
| Overscan semantics | Equations 8 and 15 have an unresolved ΔC/ΔP asymmetry. No overscan theorems are attempted. |
| Float correctness | `undistortPoint_float` is not proved to approximate the exact-real definitions within any error bound. |
| OpenCV pipeline equivalence | This library formalizes the OpenLensIO model. Cross-model equivalence proofs live in `opencv_opentrackio_proofs/Pipeline/`. |
| Renderer correctness | The pipeline is verified from lens parameters to shader coordinates; what a renderer does with those coordinates is outside scope. |

---

## Module structure

| File | Role |
|------|------|
| `CoordinateTypes.lean` | `SensorPoint`, `sensorRadius`, `sensorRadius_nonneg` |
| `LensSemantics.lean` | `RadialCoefficients`, `TangentialCoefficients`, `LensSemantics`, `ValidLensSemantics` |
| `RadialPolynomial.lean` | `radialTerm`, `denominatorNonzero`, zero-coefficient identity theorems |
| `DistortionModel.lean` | `undistortPoint`, Brown-Conrady zero-identity theorems |
| `DeltaSemantics.lean` | ΔP and ΔC offset characterizations, translation commutativity |
| `ProjectionModel.lean` | `undistortFromDistorted` (Eq 4), `projection_matrix_undistort_eq` |
| `FovModel.lean` | `fovUndistortFromDistorted` (Eq 10), `fov_undistort_eq` |
| `AngleOfView.lean` | `angle_of_view_eq` — `tan(α/2) = r_u / F` |
| `ShaderCoords.lean` | Metric ↔ shader coordinate conversions and roundtrip theorems |
| `SemanticBridge.lean` | `semanticExtraction_sound` — `ValidLensSemantics` soundness |
| `InjectivityModel.lean` | Injectivity theorems for `undistortPoint`; `radialScale`, `radialDescale`; `radialTerm_pos`/`radialTerm_ne_zero`; `radialDescale_left_inverse_zero_tangential` |
| `ExecutableSemanticOracle.lean` | Float approximation layer — for differential testing only |

---

## Source

> "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"  
> SMPTE RIS, corrected 2025-09-02  
> https://ris-pub.smpte.org/ris-osvp-metadata-camdkit/res/OpenCV_to_OpenTrackIO.pdf

See also `docs/openlensio-semantics-paper.md` for a detailed treatment of the
semantic interoperability motivation, open specification questions, and scope.
