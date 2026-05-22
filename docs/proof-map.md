# Proof Map

Maps every public theorem to its source file, proof area, and what it establishes.
Helper lemmas inside namespaces are omitted; theorems in `MutationTests.lean` are
grouped rather than listed individually.

---

## OpenCV ↔ OpenLensIO Conversion (`opencv_opentrackio_proofs/`)

### Principal-point conversion (`PrincipalPointConversion.lean`)

| Theorem | What it proves |
|---------|---------------|
| `principal_point_conversion_necessary` | Universal consistency for all `x''` uniquely forces `F = (w/ws)·fx` and `ΔPx = (w/ws)·(cx − ws/2)` — the corrected formulas |
| `principal_point_conversion_iff` | 1D linear-projection consistency for all `x''` ↔ corrected `F` and `ΔPx` (necessary and sufficient) |
| `principal_point_conversion_2d_iff` | 2D linear-projection consistency for all `(x'', y'')` ↔ corrected `F`, `ΔPx`, `ΔPy` with a single scalar `F` |
| `single_focal_length_compatibility` | 2D consistency forces `(w/ws)·fx = (h/hs)·fy` — the condition under which OpenCV's separate `fx`, `fy` are representable by one `F` |
| `buggy_principal_point_conversion_inconsistent` | The erroneous formula `ΔPx = (w/ws)·cx` (missing the `−ws/2` centering term) is mathematically inconsistent with nonzero image dimensions |

### Distortion coefficient conversion (`DistortionConversion.lean`)

| Theorem | What it proves |
|---------|---------------|
| `radial_distortion_conversion` | `∀ r, k·r^(2n) = l·(F·r)^(2n)` implies `l = k/F^(2n)` (per-term, any degree) — necessary extraction |
| `tangential_q1_conversion` | `∀ x', y', p1·x'·y' = q1·(Fx')·(Fy')` implies `q1 = p1/F²` |
| `tangential_q2_conversion` | `∀ r, x', p2·(r²+2x'²) = q2·(…)` implies `q2 = p2/F²` |
| `whole_radial_polynomial_iff` | Full numerator polynomial equal for all `r` ↔ `l1=k1/F²`, `l3=k2/F⁴`, `l5=k3/F⁶` |
| `whole_tangential_field_iff` | Full tangential `δx` equal for all `(x', y')` ↔ `q1=p1/F²`, `q2=p2/F²` |
| `whole_tangential_field_2d_iff` | Full tangential vector `(δx, δy)` equal for all `(x', y')` ↔ same conversions |
| `all_distortion_conversions_iff` | Both radial polynomials and 2D tangential field equal ↔ all 8 parameter conversions |
| `radial_coefficients_imply_rational_factor_equality` | Coefficient conversions → rational radial scale factors agree pointwise |

### Pixel coordinate equivalence (`PixelEquivalence.lean`)

| Theorem | What it proves |
|---------|---------------|
| `linear_projection_pixel_equivalence_2d_iff` | Linear projection agrees for all `(x, y)` ↔ principal-point conversions hold |
| `radial_distortion_value_equivalence` | Rational radial scale factor agrees at corresponding radii; OTI denominator nonzero iff CV denominator nonzero |

### Full pipeline equivalence (`Pipeline/`)

| Theorem | File | What it proves |
|---------|------|---------------|
| `opencv_openlensio_radial_pipeline_eq` | `RadialPipeline.lean` | Radial-only pipelines agree at corresponding points after coefficient conversion |
| `opencv_openlensio_full_pipeline_pixel_sufficiency` | `PixelSufficiency.lean` | Given all conversions and `ws/w = fx`, full x-pixel outputs agree for all normalised inputs |
| `opencv_openlensio_full_pipeline_pixel_iff` | `PixelIff.lean` | Given all conversions and `p1≠0 ∨ p2≠0`, full x-pixel outputs agree for all normalised inputs **iff** `ws/w = fx` |

### Mutation tests (`MutationTests.lean`)

40 theorems in pairs: each wrong-formula variant either (a) forces a degenerate
coefficient relationship, or (b) is outright inconsistent with the full polynomial
identity. Variants covered: wrong `ΔPx` offset form (3 pairs), wrong focal-length
scaling power for each of l1–l6 and q1–q2 (12 pairs), coefficient swaps l1↔k2,
q1↔p2, q2↔p1 (3 pairs).

---

## OpenLensIO Semantics (`openlensio_semantics/`)

| Theorem | File | What it proves |
|---------|------|---------------|
| `sensorRadius_nonneg` | `CoordinateTypes.lean` | `sensorRadius p ≥ 0` for all sensor points |
| `radial_denominator_nonzero_zero_coeffs` | `RadialPolynomial.lean` | Zero denominator coefficients make denominator identically 1 |
| `radial_zero_coefficients_identity` | `RadialPolynomial.lean` | Zero radial coefficients make `radialTerm = 1` |
| `tangential_zero_coefficients_identity` | `DistortionModel.lean` | Zero tangential coefficients make the tangential correction zero |
| `brown_conrady_zero_identity` | `DistortionModel.lean` | All-zero coefficients reduce `undistortPoint` to the identity |
| `deltaP_characterisation` | `DeltaSemantics.lean` | Characterizes ΔP sign convention: `ε_d = ε'_d + ΔP` |
| `deltaC_characterisation` | `DeltaSemantics.lean` | Characterizes ΔC offset in the undistortion argument |
| `distortion_center_translation_commutes` | `DeltaSemantics.lean` | ΔP cancels when substituting Eq 13, leaving both forms applying U to the same point |
| `projection_matrix_undistort_eq` | `ProjectionModel.lean` | Projection-matrix form (Eq 4) structural consistency |
| `fov_undistort_eq` | `FovModel.lean` | FOV form (Eq 10) agrees with projection form under Eq 13 translation |
| `angle_of_view_eq` | `AngleOfView.lean` | `tan(α/2) = r_u / F` (Eq 18) |
| `pixel_metric_roundtrip` | `ShaderCoords.lean` | Metric → shader → metric is the identity |
| `image_texture_coordinate_roundtrip` | `ShaderCoords.lean` | Shader → metric → shader is the identity |
| `semanticExtraction_sound` | `SemanticBridge.lean` | Extracted lens parameters satisfy `ValidLensSemantics` (`0 < focalLength`) |

---

## OpenTrackIO Parser (`opentrackio_parser/`)

### Foundation

| Theorem | File | What it proves |
|---------|------|---------------|
| `lookup?_some_implies_field_present` | `JsonRawModel.lean` | `lookup?` returning `some` implies key exists in object |
| `lookup?_none_implies_no_matching_field` | `JsonRawModel.lean` | `lookup?` returning `none` implies no matching key |
| `rational_with_positive_denominator_den_ne_zero` / `_den_nat_ne_zero` | `RationalValueWrappers.lean` | Type-carried denominator nonzero facts |
| `positive_rational_num_ne_zero`, `positive_rational_toReal_pos` | `RationalValueWrappers.lean` | Type-carried positivity facts |
| `nonnegative_rational_toReal_nonneg` | `RationalValueWrappers.lean` | Type-carried nonnegativity |
| `protocolVersion_valid` | `ProtocolVersion.lean` | Every `ProtocolVersion` satisfies `ValidVersion` |

### Decoder soundness

| Theorem | File | What it proves |
|---------|------|---------------|
| `decodePositiveRational_sound` | `RationalDecoder.lean` | Decoded rational has `num > 0`, `den > 0` |
| `decodeNonemptyArray_sound` | `NonemptyArrayDecoder.lean` | Decoded array is nonempty |
| `decodeTimingMode_sound` (and 3 analogues) | `TimingEnumDecoders.lean` | Enum decoders accept only known string literals; roundtrip with `toStr` |
| `decodeVersionValue_sound` | `VersionDecoder.lean` | Decoded version digits are in `Fin 10` |
| `decodeProtocol_sound` | `ProtocolDecoder.lean` | Protocol satisfies `ValidVersion` |
| `decodeTransform_sound` | `TransformDecoder.lean` | Decoded transform satisfies structural invariants |
| `decodeCamera_sound` | `CameraDecoder.lean` | Decoded camera satisfies structural invariants |
| `decodeLens_sound` | `LensDecoder.lean` | Decoded lens satisfies `FizOptions.anyPresent` and coefficient array invariants |
| `decodeSample_transforms_sound` | `SampleDecoder.lean` | Decoded sample's transform arrays are nonempty |
| `decodeSample_protocol_sound` | `SampleDecoder.lean` | Decoded sample's protocol satisfies `ValidVersion` |
| `decodeSample_lens_encoders_sound` | `SampleDecoder.lean` | Decoded sample's lens encoder group has at least one of focus/iris/zoom |
| `decodeSample_static_duration_sound` | `SampleDecoder.lean` | Decoded static duration rational is positive |
| `decodeSample_static_camera_sound` | `SampleDecoder.lean` | Decoded static camera frame-rate rational is positive |

### Error correctness

| Theorem | File | What it proves |
|---------|------|---------------|
| `decodeProtocol_missing_name` | `ErrorCorrectness.lean` | Missing `name` field → `.error (.missingField "name")` |
| `decodeProtocol_missing_version` | `ErrorCorrectness.lean` | Missing `version` field → expected error |
| `decodeTransform_missing_translation` | `ErrorCorrectness.lean` | Missing `translation` → expected error |
| `decodeTransform_missing_rotation` | `ErrorCorrectness.lean` | Missing `rotation` → expected error |
| `decodePositiveRational_missing_num` | `ErrorCorrectness.lean` | Missing `num` field → expected error |

### Encode/decode roundtrip

| Theorem | File | What it proves |
|---------|------|---------------|
| `nat_repr_toNat?_some` | `NumericLiteralRoundtrip.lean` | Lean's decimal renderer and `String.toNat?` are inverses for all naturals |
| `encodeVersionDigit_roundtrip` / `encodeVersionValue_roundtrip` / `encodeProtocol_roundtrip` | `VersionEncoder.lean` | Protocol version encode → decode is identity |
| `encodePositiveRational_roundtrip` | `TimecodeEncoder.lean` | Rational encode → decode is identity |
| `encodeVec3_roundtrip` / `encodeRotation_roundtrip` / `encodeTransform_roundtrip` | `TransformEncoder.lean` | Transform encode → decode is identity |
| `encodeCamera_roundtrip` / `encodeSensorResolution_roundtrip` | `CameraEncoder.lean` | Camera encode → decode is identity |
| `encodeFizOptions_roundtrip` / `encodeDistortion_roundtrip` (and sub-encoders) | `LensSubEncoders.lean` | Lens sub-object encode → decode is identity |
| `encodeStaticLens_roundtrip` / `encodeLens_roundtrip` | `LensEncoder.lean` | Full lens encode → decode is identity |
| `encodeGlobalStage_roundtrip` / `encodeTracker_roundtrip` / `encodeTiming_roundtrip` / `encodeSynchronization_roundtrip` / `encodePtpInfo_roundtrip` | Various encoders | Sub-sample encode → decode is identity |
| `encodeSample_roundtrip` | `SampleEncoder.lean` | **Top-level:** encoding any `Sample` and decoding returns the original |

### Normalization

| Theorem | File | What it proves |
|---------|------|---------------|
| `encodedSample_stable` | `NormalizationTheorems.lean` | Encoded samples are already normalized |
| `sampleNormalize_idempotent` | `NormalizationTheorems.lean` | `sampleNormalize ∘ sampleNormalize = sampleNormalize` |
| `sampleNormalize_encodeSample` | `NormalizationTheorems.lean` | Normalizing an encoded sample is a no-op |
| `wellFormed_normalize_eq_encode` | `NormalizationTheorems.lean` | For well-formed inputs that decode to `s`, normalizing gives the same JSON as encoding `s` |
| `normalization_under_wellFormed` | `NormalizationTheorems.lean` | Normalization preserves decoded semantics for well-formed inputs |
