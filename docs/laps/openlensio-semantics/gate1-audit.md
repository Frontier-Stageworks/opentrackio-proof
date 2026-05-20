---
name: openlensio-semantics-gate1-audit
description: Gate 1 audit — actual parser type inventory and existing OpenCV proof theorem inventory; confirms no duplication before SLICE-OL-01
metadata:
  type: reference
---

# Gate 1 Audit — `openlensio_semantics`

**Status: PASSED**  
**Toolchain:** `leanprover/lean4:v4.29.0`, Mathlib `v4.29.0`

---

## Parser model types (from actual source)

### `TransformModel.lean`

| Type | Fields |
|------|--------|
| `NonemptyString` | `val : String`, `nonempty : val ≠ ""` |
| `Vec3` | `x y z : String` (raw JSON number strings) |
| `Rotation` | `pan tilt roll : String` (degrees, unbounded) |
| `Transform` | `translation : Vec3`, `rotation : Rotation`, `scale : Option Vec3`, `id : Option NonemptyString` |

### `RationalValueWrappers.lean`

| Type | Fields | Invariant |
|------|--------|-----------|
| `RationalWithPositiveDenominator` | `num : Int`, `den : Nat`, `den_pos : 0 < den` | `den > 0` |
| `NonnegativeRational` | `num : Nat`, `den : Nat`, `den_pos : 0 < den` | `den > 0`, `num ≥ 0` |
| `PositiveRational` | `num : Nat`, `den : Nat`, `num_pos : 0 < num`, `den_pos : 0 < den` | `num > 0`, `den > 0` |

All three have `.toReal : ℝ` (noncomputable) and denominator/numerator theorems.

**Key observation:** `PositiveRational` carries invariants at the type level via `num_pos` and `den_pos`. It is decoded from JSON objects `{num, den}` — NOT from plain number strings.

### `CameraModel.lean`

| Type | Fields |
|------|--------|
| `SensorPhysicalDimensions` | `height width : String` (raw JSON number strings, mm) |
| `SensorResolution` | `height width : Nat` |
| `Camera` | 12 optional fields; `captureFrameRate anamorphicSqueeze : Option PositiveRational`; `make model serialNumber firmwareVersion label : Option NonemptyString`; rest are `Option String` or `Option Nat` |

**Key observation for sensorWidth:** `w` (sensor width in mm) lives in `Camera.activeSensorPhysicalDimensions.width : String`, not in `Lens`. The semantic bridge will need both `Lens` and `Camera` to build a full projection context.

### `LensModel.lean`

| Type | Fields |
|------|--------|
| `FizOptions` | `focus iris zoom : Option String`, `anyPresent : focus ≠ none ∨ ...` |
| `DistortionOffset` | `x y : String` (raw strings — corresponds to **ΔC** in paper) |
| `ProjectionOffset` | `x y : String` (raw strings — corresponds to **ΔP** in paper) |
| `ExposureFalloff` | `a1 : String`, `a2 a3 : Option String` |
| `Distortion` | `radial : NonemptyArray String`, `tangential : Option (NonemptyArray String)`, `overscan : Option String`, `model : String` |
| `StaticLens` | 8 optional fields including `distortionOverscanMax undistortionOverscanMax : Option String` |
| `Lens` | 12 optional fields (see below) |

**`Lens` field inventory (complete):**

| Field | Type | Paper mapping |
|-------|------|---------------|
| `custom` | `Option (List String)` | — |
| `distortion` | `Option (NonemptyArray Distortion)` | k₁..k₆, p₁, p₂, overscan |
| `distortionOffset` | `Option DistortionOffset` | ΔC |
| `encoders` | `Option FizOptions` | — |
| `entrancePupilOffset` | `Option String` | z_epd (Eq 1) |
| `exposureFalloff` | `Option ExposureFalloff` | α₁..α₃ (vignetting, deferred) |
| `fStop` | `Option String` | — |
| `focusDistance` | `Option String` | Φ (aperture, deferred) |
| `pinholeFocalLength` | `Option String` | **F** (raw number string) |
| `projectionOffset` | `Option ProjectionOffset` | **ΔP** |
| `rawEncoders` | `Option FizOptions` | — |
| `tStop` | `Option String` | — |

**Critical finding:** ALL numeric fields in `Lens` are raw `String` or `Option String`. `PositiveRational` is NOT used in `Lens`. The semantic bridge must parse these strings to `ℝ` values. The existing `decodePositiveRational` only handles `{num, den}` JSON objects — it cannot parse plain decimal strings.

**Critical finding:** `Distortion.radial : NonemptyArray String` — the radial coefficients k₁..k₆ are stored as a nonempty array of strings with NO fixed length enforced at the parser level. The semantic bridge must validate that exactly 6 elements are present (or handle shorter arrays).

### `SampleModel.lean`

| Type | Relevant fields |
|------|----------------|
| `Sample` | `lens : Option Lens`, `static : Option StaticInfo` |
| `StaticInfo` | `camera : Option Camera`, `lens : Option StaticLens`, ... |

---

## Existing OpenCV proof theorems (from actual source)

### `PrincipalPointConversion.lean`

| Theorem | What it proves |
|---------|---------------|
| `principal_point_conversion_necessary` | Consistency for all x'' forces unique F and ΔPx formulas |
| `principal_point_conversion_iff` | 1D iff version |
| `principal_point_conversion_2d_iff` | 2D iff version |
| `single_focal_length_compatibility` | 2D consistency forces both axes to agree on F |
| `buggy_principal_point_conversion_inconsistent` | Prior erroneous formula is provably wrong |

**Scope:** All theorems are about the OpenCV ↔ OpenTrackIO principal-point conversion formula. They prove the conversion is forced by the requirement that both models assign the same pixel to every scene point.

### `DistortionConversion.lean`

| Theorem | What it proves |
|---------|---------------|
| `radial_distortion_conversion` | Per-term: k*r^(2n) = l*(F*r)^(2n) → l = k/F^(2n) |
| `tangential_q1_conversion` | Cross term p1 scaling |
| `tangential_q2_conversion` | Radial+squared term p2 scaling |
| `whole_radial_polynomial_iff` | Full OpenCV numerator polynomial = OpenTrackIO iff coefficients |
| `whole_tangential_field_iff` | Full δx field iff (1D) |
| `whole_tangential_field_2d_iff` | Full 2D tangential vector iff |
| `all_distortion_conversions_iff` | All 8 parameters, full model iff |
| `radial_coefficients_imply_rational_factor_equality` | Rational factor value equal at r when conversions hold |

**CRITICAL NAMING NOTE:** `DistortionConversion.lean` uses a DIFFERENT naming convention from the OpenLensIO paper:
- In `DistortionConversion.lean`: k1,k2,k3 = **OpenCV numerator** coefficients; k4,k5,k6 = **OpenCV denominator** coefficients
- In the OpenLensIO paper (Eq 17): k1,k3,k5 = **numerator** coefficients; k2,k4,k6 = **denominator** coefficients (alternating)

The `openlensio_semantics` project must use the **paper's naming** (alternating k1/k2/k3/k4/k5/k6). Structures must not use `DistortionConversion`'s naming convention.

**Scope:** All theorems are about the OpenCV ↔ OpenTrackIO *conversion* of distortion parameters. They do NOT prove anything about the OpenLensIO distortion function itself. They prove the conversion scaling law.

### `PixelEquivalence.lean`

| Theorem | What it proves |
|---------|---------------|
| `linear_projection_pixel_equivalence_2d_iff` | Linear (no distortion) pipeline equivalence iff — restates `principal_point_conversion_2d_iff` |
| `radial_distortion_value_equivalence` | OpenTrackIO rational radial scale = OpenCV scale at corresponding radii, PLUS OpenTrackIO denominator nonzero when OpenCV denominator is |

**Scope:** `radial_distortion_value_equivalence` proves the OpenTrackIO denominator is nonzero GIVEN the OpenCV denominator is nonzero and the conversion formulas hold. This is in the OpenCV↔OpenTrackIO conversion context. The `openlensio_semantics` project needs a standalone denominator safety theorem for the OpenLensIO model — different theorem, different context. **No duplication.**

---

## Duplication audit

| Proposed `openlensio_semantics` theorem | Existing theorem? | Conclusion |
|-----------------------------------------|-------------------|-----------|
| `semanticExtraction_sound` | None | New |
| `sensorRadius_nonneg` | None | New |
| `radial_zero_coefficients_identity` | None | New (different from `radial_coefficients_imply_rational_factor_equality`) |
| `brown_conrady_zero_identity` | None | New |
| `pixel_metric_roundtrip` (Eq 18 only) | `linear_projection_pixel_equivalence_2d_iff` covers the full pipeline (projection + shader). Eq 18 alone is the coordinate conversion sub-step. | New — no duplication, scope is narrower |
| `radial_denominator_nonzero_under_constraints` | `radial_distortion_value_equivalence` derives denominator nonzero GIVEN the OpenCV denominator is nonzero. Different context. | New |
| `projection_matrix_undistort_eq` | None | New |
| `tangential_zero_coefficients_identity` | None | New |

**Conclusion: No duplication identified. SLICE-OL-01 may open.**

---

## Implementation order correction

The work-queue listed CoordinateTypes (OL-04) after LensSemantics (OL-01), but `LensSemantics` uses `SensorPoint` for `distCentre` and `perspOffset`. Actual file creation order:

1. `CoordinateTypes.lean` (OL-04 — needed by OL-01)
2. `LensSemantics.lean` (OL-01)
3. `SemanticBridge.lean` (OL-02 + OL-03)

This does not change the conceptual layer ordering. It is a file dependency only.

---

## Gate 1 pass decision

All pass criteria satisfied:
- [x] SLICE-OL-03 will not re-prove JSON key name correctness
- [x] SLICE-OL-05 will not re-prove OpenCV↔OTio distortion coefficient conversion
- [x] SLICE-OL-13 will not re-prove pixel-coordinate preservation from `PixelEquivalence.lean`
- [x] Parser model field names and types read from source (`pinholeFocalLength : Option String`, etc.)
- [x] All three OpenCV proof files inventoried; naming convention difference noted; no duplication found

**Gate 1: PASSED. SLICE-OL-01 may open after Gates 2 and 3.**
