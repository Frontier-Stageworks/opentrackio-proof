# Proof Review: opentrackio-proof — Whole-Repo Audit

## Verdict

**accepted with notes — process evidence incomplete**

Semantic review passes across all three modules. No forbidden constructs. No
vacuity. Notes flag: (1) `deltaP_characterisation` / `deltaC_characterisation`
are documented α-equivalents retained for paper traceability; (2) junk-value
semantics at F=0 in `angle_of_view_eq` (benign, documented); (3) `IntegrationSmoke.lean`
uses `#eval` runtime checks — correctly scoped as smoke tests, not proof
substitutes. Process evidence is incomplete: `lake build` was not run in this
session; final Lean result is unknown.

---

## REVIEW EVIDENCE

```
REVIEW EVIDENCE:
- Repo path / identifier:    /Users/markstalzer/github/opentrackio-proof
- Repo commit:               18cfc3b
- LAPS version:              updated (2026-05-23)
- Review date:               2026-05-23
- Review scope:              all 65 Lean source files, 3 modules
- Review type:               exhaustive theorem audit
- Final Lean command:        lake build (not run in this session)
- Final Lean result:         unknown / not available
- Warnings:                  unknown / not available (build not run)
- Forbidden construct scan command(s):
    grep -rn "sorry|admit|set_option warn.sorry|^unsafe|^partial" --include="*.lean" (excluding .lake/)
    grep -rn "^axiom|^constant" --include="*.lean" (excluding .lake/)
- Forbidden construct scan result:
    sorry/admit/unsafe/partial: NONE FOUND (0 matches)
    axiom/constant:             NONE FOUND (0 matches)
    sorry-warning suppression:  NONE FOUND (0 matches)
- Lean files reviewed:       65 (all source files; 40 opentrackio_parser, 11 openlensio_semantics, 10 opencv_opentrackio_proofs + 4 Pipeline/)
- Theorem declarations reviewed: ~110 public theorem/lemma declarations
- Theorem inventory:         see Theorem Inventory section below
- Artifact freshness:
    proof-capsule.md: n/a (whole-repo audit)
    proof-plan.md:    n/a
    work-queue.md:    n/a
    proof-run-log.md: n/a
- metrics.md required:       yes (large task)
- metrics.md finalized:      yes (docs/laps/whole-repo-review/metrics.md)
```

---

## Theorem Inventory

### Module: `opentrackio_parser/` (~67 public theorems)

| File | Theorems |
|---|---|
| RationalValueWrappers.lean | rational_with_positive_denominator_den_nat_ne_zero, nonneg_rational_den_nat_ne_zero, positive_rational_den_nat_ne_zero, rational_with_positive_denominator_den_ne_zero, nonneg_rational_den_ne_zero, positive_rational_den_ne_zero, positive_rational_num_ne_zero, positive_rational_toReal_pos, nonnegative_rational_toReal_nonneg |
| JsonRawModel.lean | lookup?_some_implies_field_present, lookup?_none_implies_no_matching_field |
| ProtocolVersion.lean | protocolVersion_valid |
| NonemptyArrayDecoder.lean | decodeNonemptyArray_sound |
| NumericLiteralRoundtrip.lean | nat_repr_toNat?_some (+ 8 private helpers) |
| SynchronizationEncoder.lean | encodeSynchronization_roundtrip |
| GlobalStageEncoder.lean | encodeGlobalStage_roundtrip |
| TimecodeEncoder.lean | encodePositiveRational_roundtrip, encodeTimecode_roundtrip |
| TransformEncoder.lean | encodeVec3_roundtrip, encodeRotation_roundtrip, encodeTransform_roundtrip |
| VersionEncoder.lean | encodeVersionDigit_roundtrip, encodeVersionValue_roundtrip, encodeProtocol_roundtrip |
| SampleDecoder.lean | decodeSample_transforms_sound, decodeSample_protocol_sound, decodeSample_lens_encoders_sound, decodeSample_static_duration_sound, decodeSample_static_camera_sound |
| CameraEncoder.lean | encodeSensorPhysicalDimensions_roundtrip, encodeSensorResolution_roundtrip, encodeCamera_roundtrip |
| NormalizationTheorems.lean | sampleNormalize_idempotent, encodedSample_stable, sampleNormalize_encodeSample, wellFormed_normalize_eq_encode, normalization_under_wellFormed |
| RationalDecoder.lean | decodePositiveRational_sound |
| LensEncoder.lean | encodeStaticLens_roundtrip, encodeLens_roundtrip |
| PtpInfoEncoder.lean | encodePtpInfo_roundtrip |
| SampleEncoder.lean | encodeSample_roundtrip |
| ErrorCorrectness.lean | decodeProtocol_missing_name, decodeProtocol_missing_version, decodeTransform_missing_translation, decodeTransform_missing_rotation, decodePositiveRational_missing_num |
| LeafEncoders.lean | encodeTimestamp_roundtrip, encodeLeaderPriorities_roundtrip, encodeSyncOffsets_roundtrip |
| TransformDecoder.lean | decodeTransform_sound |
| TimingEnumDecoders.lean | decodeTimingMode_sound, decodeSyncSource_sound, decodePtpProfile_sound, decodePtpLeaderSource_sound |
| TrackerEncoder.lean | encodeStaticTracker_roundtrip, encodeTracker_roundtrip |
| CameraDecoder.lean | decodeCamera_sound |
| VersionDecoder.lean | decodeVersionValue_sound |
| ProtocolDecoder.lean | decodeProtocol_sound |
| LensSubEncoders.lean | encodeFizOptions_roundtrip, encodeDistortionOffset_roundtrip, encodeProjectionOffset_roundtrip, encodeExposureFalloff_roundtrip, encodeDistortion_roundtrip |
| TimingEncoder.lean | encodeTiming_roundtrip |
| LensDecoder.lean | decodeLens_sound |
| IntegrationSmoke.lean | 0 theorems — #eval smoke tests only (see note below) |

### Module: `openlensio_semantics/` (~14 public theorems)

| File | Theorems |
|---|---|
| CoordinateTypes.lean | sensorRadius_nonneg |
| RadialPolynomial.lean | radial_denominator_nonzero_zero_coeffs, radial_zero_coefficients_identity |
| DistortionModel.lean | tangential_zero_coefficients_identity, brown_conrady_zero_identity |
| DeltaSemantics.lean | deltaP_characterisation, deltaC_characterisation, distortion_center_translation_commutes |
| SemanticBridge.lean | semanticExtraction_sound |
| AngleOfView.lean | angle_of_view_eq |
| ShaderCoords.lean | pixel_metric_roundtrip, image_texture_coordinate_roundtrip |
| FovModel.lean | fov_undistort_eq |
| ProjectionModel.lean | projection_matrix_undistort_eq |

### Module: `opencv_opentrackio_proofs/` (~30 public theorems/lemmas)

| File | Theorems |
|---|---|
| DistortionConversion.lean | radial_distortion_conversion, tangential_q1_conversion, tangential_q2_conversion, whole_radial_polynomial_iff, whole_tangential_field_iff, whole_tangential_field_2d_iff, all_distortion_conversions_iff, radial_coefficients_imply_rational_factor_equality |
| PrincipalPointConversion.lean | principal_point_conversion_necessary, principal_point_conversion_iff, principal_point_conversion_2d_iff, single_focal_length_compatibility, buggy_principal_point_conversion_inconsistent |
| PixelEquivalence.lean | linear_projection_pixel_equivalence_2d_iff, radial_distortion_value_equivalence |
| MutationTests.lean | 24 mutation theorems (groups A–H) + 2 sanity examples (I.1, I.2) |
| Pipeline/PixelIffHelpers.lean | radial_ratio_scaled_eq, tangential_scaled_eq, principal_offset_cancels, tangential_gap_forces_scale, pixel_eq_implies_tangential_gap (5 lemmas, PipelineEquivalence namespace) |
| Pipeline/PixelSufficiency.lean | opencv_openlensio_full_pipeline_pixel_sufficiency |
| Pipeline/PixelIff.lean | opencv_openlensio_full_pipeline_pixel_iff |
| Pipeline/RadialPipeline.lean | opencv_openlensio_radial_pipeline_eq |

---

## Theorem-by-Theorem Audit

### GROUP 1 — opentrackio_parser: Infrastructure theorems

#### `lookup?_some_implies_field_present` / `lookup?_none_implies_no_matching_field`

**Plain English:** A successful `lookup?` result implies `hasField`; a `none`
result implies `¬hasField`. Both are definitional consequences of `hasField`'s
definition as `lookup? k ≠ none`.

**Proof Strategy:** `simp only` reduces both goals to trivial propositions.
`Option.some_ne_none` closes the first. Both are appropriate: automation is
goal-shaped and the conclusions follow directly from the definitions.

**Anti-pattern scan:** no issues. Not test-shaped (universally quantified over
all `j : JsonValue` and `k : String`). Conclusions are not proxies — they are
exactly the intended API contracts for `hasField`.

**Verdict:** accepted

---

#### `rational_with_positive_denominator_den_nat_ne_zero` and family (9 theorems)

**Plain English:** The denominator fields of the three rational wrapper structs
are nonzero (both at Nat level and ℝ level); `PositiveRational` additionally has
positive numerator and positive real value; `NonnegativeRational` has nonneg
real value.

**Parameter audit:** all theorems take exactly the struct `r` as input and
project its invariant fields (`r.den_pos`, `r.num_pos`). No suspicious
hypotheses.

**Proof Strategy:** `omega` for Nat-level; `exact_mod_cast` for ℝ-level coercion;
`div_pos` + `exact_mod_cast` for `positive_rational_toReal_pos`; `positivity`
for `nonnegative_rational_toReal_nonneg`.

**Automation review:** all automation is goal-shaped. `exact_mod_cast` is the
right tool for the Nat→ℝ coercion. `positivity` for `nonneg` is appropriate.

**Verdict:** accepted

---

### GROUP 2 — opentrackio_parser: Core proof chain

#### `nat_repr_toNat?_some`

**Theorem Statement:**
```lean
theorem nat_repr_toNat?_some (n : Nat) :
    n.repr.toNat? = some n
```

**Plain English:** For every natural number `n`, rendering it as its decimal
string and parsing that string back as a natural number recovers exactly `n`.

**Intended claim match:** yes — this is the foundational bridge that all Nat-field
encoder roundtrip proofs depend on.

**Parameter and Hypothesis Audit:**

| Name | Type / Role | Used? | Necessary? | Suspicious? | Notes |
|---|---|---|---|---|---|
| `n : Nat` | number to round-trip | yes | yes | no | universally quantified |

**Conclusion Audit:**
- Conclusion is strong enough: yes — equality `= some n`, not mere existence
- Conclusion is not a proxy: yes — the direct claim
- Conclusion is not test-shaped: yes — universal over all Nat

**Proof Strategy:**
- First meaningful tactic: `simp only [Nat.repr, String.toNat?, String.Slice.toNat?]`
- Expected proof shape: unfold definitions, delegate to 8-lemma helper chain
- Strategy matches theorem shape: yes

**Hard Step:** `foldl_toDigits` (H6): strong induction on `n` proving the fold
accumulator recovers `n`. Load-bearing bridge: `toDigitsCore_eq` (H3), which
connects `Nat.toDigitsCore` (fuel loop) to `Nat.toDigits` (inductive definition).

**Automation Review:**
- `interval_cases` for base cases (n < 10): appropriate
- `omega` for arithmetic bounds: appropriate
- `decide` for concrete character comparisons: appropriate
- The hard step (digit recovery) uses structured induction; automation is localized

**Anti-Pattern Scan:**

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Vacuity | no | | |
| Weakened conclusion | no | full equality `= some n` | |
| Tactic soup | no | clean H1–H8 helper layering | |
| Broad automation hiding hard step | no | induction exposed; automation localized | |

**Forbidden Construct Check:** absent across all fields

**Verdict:** accepted

---

#### `encodeSample_roundtrip` and the encoder-roundtrip chain (Slices 15.1–15.11)

**Plain English pattern (all roundtrip theorems):** Encoding a typed value and
immediately decoding it returns the original value. Pattern:
`decodeX (encodeX v) = .ok v`.

**Intended claim match:** yes — this is the central parser correctness property.
The `encodeSample_roundtrip` is the top-level capstone that the normalization
theorems consume.

**Parameter and Hypothesis Audit:** all roundtrip theorems take exactly the
typed value as input. No suspicious hypotheses.

**Proof Strategy pattern:** varies by complexity — `simp [encodeX, decodeX]`
for leaf types; `constructor` + simp-chaining for composite types; delegation
to sub-encoder roundtrips for `encodeSample_roundtrip`. All strategies match
their theorem shapes.

**Anti-Pattern Scan:**
- No test-shaped theorems: all universally quantified over the value type
- No weakened conclusions: all are `.ok v` equality, not `isOk` or existence

**Verdict:** accepted (as a family)

---

#### `sampleNormalize_idempotent` and normalization cluster (5 theorems)

**Plain English:** `sampleNormalize` (decode-then-re-encode) is idempotent;
encoding a sample produces a stable canonical form; well-formed JSON normalizes
correctly.

**Proof Strategy:** all use `encodeSample_roundtrip` as the engine.
`sampleNormalize_idempotent`: case-splits on decode success/failure and rewrites
with `encodeSample_roundtrip`. `encodedSample_stable`: trivial existential witness.
`sampleNormalize_encodeSample`: single `simp` with `encodeSample_roundtrip`.

**Hard Step:** `encodeSample_roundtrip` — imported from SampleEncoder.

**Anti-Pattern Scan:** no issues. Non-vacuous: the error branch (decode fails)
covers genuinely non-roundtrippable JSON.

**Verdict:** accepted

---

#### Error correctness theorems (5 theorems in ErrorCorrectness.lean)

**Plain English:** Each decoder returns `.error (.missingField "name")` when the
named required field is absent from the object.

**Proof Strategy:** `simp [decodeX, h]` where `h` is the `lookup? "field" = none`
hypothesis. Appropriate: decoder definitions are transparent to `simp` and the
goals are shallow structural claims.

**Hypothesis audit:**
- `decodeTransform_missing_rotation` carries `tj : JsonValue` via `ht`. The value
`tj` is not referenced in the proof but is necessary to state the field-present
precondition for translation. Load-bearing, not suspicious.

**Anti-Pattern Scan:**

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Test-shaped | no | universal over all `kvs : List (String × JsonValue)` | |
| Unused hypotheses | minor | `tj` in decodeTransform_missing_rotation — structurally necessary | low |

**Verdict:** accepted

---

#### `IntegrationSmoke.lean` — smoke test assessment

This file contains `#eval` expressions and a `smokeSample` definition, but **zero
theorems**. The `#eval` calls are runtime evaluation checks, not proofs. The file
header correctly states "No new theorems. No sorry."

**Anti-Pattern Flag:** potential verifier confusion risk if `#eval` results (which
return a `Bool`) were treated as proof of decoder correctness. However the file
is correctly scoped — it tests that the system elaborates without error and that
representative inputs produce `.isOk`. It does not substitute for formal proofs.

**Verdict:** no proof to accept/reject. Correctly scoped. Low risk.

---

### GROUP 3 — openlensio_semantics

#### `deltaP_characterisation` / `deltaC_characterisation` (flagged α-equivalence)

**Theorem Statements:**
```lean
theorem deltaP_characterisation (ε'_u ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_u ΔP) ΔP = ε'_u

theorem deltaC_characterisation (ε'_d ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_d ΔP) ΔP = ε'_d
```

**Plain English:** Shifting a sensor point by ΔP and then un-shifting returns the
original point. Both theorems state `(a + b) - b = a` for SensorPoint arithmetic.

**Intended Claim Match:** yes — these formalize §3 Eqs (12) and (13).

**⚠ Flagged: documented α-equivalence.** The file itself identifies this as audit
finding VAC-01: the two theorems are formally α-equivalent (identical statement
and proof, different bound variable names). The duplication is intentional for
paper-equation traceability. This is **not a defect** but is a design choice that
a future maintainer should be aware of. A single generic vector-shift theorem
would formally suffice.

**Proof Strategy:** `ext <;> simp [addSensorPoints, subSensorPoints]`. Correct
and goal-shaped.

**Anti-Pattern Scan:**

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Statement laundering | no | both trace to distinct paper equations | |
| Duplicated theorem | yes (documented) | VAC-01 flag in file | low — intentional |

**Verdict:** accepted with notes (documented α-equivalence, retained for traceability)

---

#### `distortion_center_translation_commutes`

**Plain English:** `(ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC`. The ΔP terms cancel,
so both parametrizations (Eq 4 and Eq 10) feed U the same distortion-centred argument.

**Hard Step:** none — follows by `ring` after `ext` and simp unfolding. This is
the load-bearing bridge used by `fov_undistort_eq`.

**Verdict:** accepted

---

#### `semanticExtraction_sound`

**Plain English:** A successful `extractLensSemantics` call guarantees the result
satisfies `ValidLensSemantics` (focal length > 0).

**Non-vacuity:** F ≤ 0 inputs return `.error`, so the `.ok` branch is genuinely
constrained. The hypothesis `h : extractLensSemantics ... = .ok s` is satisfiable
only for F > 0.

**Proof Strategy:** `unfold extractLensSemantics at h` + `split_ifs at h with hf`.
Positive branch: `simp only [Except.ok.injEq] at h` + `subst h` + `exact hf`.
Error branch closes automatically from contradictory `h`.

**Verdict:** accepted

---

#### `angle_of_view_eq`

**Theorem Statement:**
```lean
theorem angle_of_view_eq (F r_u : ℝ) :
    Real.tan (angleOfView F r_u / 2) = r_u / F
```

**Plain English:** The tangent of half the angle of view equals r_u / F.

**Proof Strategy:** `simp [angleOfView, Real.tan_arctan]`. Unfolds
`angleOfView = 2 * arctan(r_u/F)`, halves, applies `Real.tan_arctan`.

**⚠ Junk-value semantics at F = 0:** At F=0, Lean's total division gives
`r_u / 0 = 0` and `arctan(0) = 0`, so both sides equal 0. The theorem holds
but is physically meaningless at F=0. The file documents this and delegates
physical enforcement to `ValidLensSemantics`. Benign design choice.

**Conclusion Audit:**
- Conclusion strong enough: yes for physical domain (F > 0)
- Not a proxy: yes
- Not test-shaped: yes — universal over all F, r_u : ℝ

**Verdict:** accepted with notes (junk-value at F=0; documented; caller-enforced)

---

#### `pixel_metric_roundtrip` / `image_texture_coordinate_roundtrip`

**Plain English:** The shader-coordinate functions `toShaderCoords` and
`fromShaderCoords` are mutual inverses.

**Hypothesis Audit:** `hw : 0 < w`, `hh : 0 < h`, `hs : 0 < wshader` — all three
are load-bearing for `field_simp`. Stronger than `≠ 0` as required by the physical
domain.

**Proof Strategy:** `ext <;> simp [...] <;> field_simp [...] <;> ring`. Correct
and goal-shaped.

**Verdict:** accepted

---

#### `projection_matrix_undistort_eq`

**Plain English:** Stripping the ΔC+ΔP offset from `undistortFromDistorted`'s
output recovers `undistortPoint`'s output — i.e., `(a + b + c) - b - c = a`.

**Scope limitation (explicitly documented):** This is an algebraic consistency
check of the offset-wrapping structure, NOT full Eq(3)/Eq(4) forward/inverse
equivalence. The file correctly identifies what is and is not proved.

**Proof Strategy:** `ext <;> simp [...] <;> ring`. Appropriate for a purely
algebraic claim.

**Verdict:** accepted

---

#### `fov_undistort_eq`

**Plain English:** When the distorted coordinate is shifted by ΔP
(`ε_d = ε'_d + ΔP`), `undistortFromDistorted` equals `fovUndistortFromDistorted`
plus ΔP.

**Hypothesis Audit:** Two separate denominator-nonzero proofs (`h` and `h'`) are
required because the two definitions apply `undistortPoint` at
propositionally-equal but definitionally-distinct `SensorPoint` expressions. This
is an implementation artifact of Lean's definitional equality, not a logical
weakness. The private `undistortPoint_congr` helper correctly bridges the gap
using `subst` + proof irrelevance.

**Anti-Pattern Scan:**

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Over-strong hypotheses | no | both h/h' are structurally necessary | |
| Implementation artifact | noted | h' arises from Lean definitional equality | low |

**Verdict:** accepted

---

### GROUP 4 — opencv_opentrackio_proofs

#### `principal_point_conversion_necessary` through `buggy_principal_point_conversion_inconsistent` (5 theorems)

**Key theorems:**

`principal_point_conversion_2d_iff` — the 2D camera-model iff:
```lean
theorem principal_point_conversion_2d_iff ... :
    (∀ x'' y'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2 ∧
        fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2) ↔
    F = (w / w_shader) * fx ∧ ΔPx = (w / w_shader) * (cx - w_shader / 2) ∧
    F = (h / h_shader) * fy ∧ ΔPy = (h / h_shader) * (cy - h_shader / 2)
```

**Plain English:** The OpenCV and OpenTrackIO linear projections agree for all
scene points in both axes iff the published principal-point conversion formulas hold.

**Hard Step:** `principal_point_conversion_necessary` — specialization at x''=0
(intercept) and x''=1 (slope + intercept), then `nlinarith` closes.

`buggy_principal_point_conversion_inconsistent` — the regression guard: the old
formula `ΔPx = (w/ws)·cx` (missing the centering term) forces `ws = 0`,
contradicting `hws`. This is a strong, non-proxy theorem with clear intent and
historical motivation (documented SMPTE RIS paper bug).

`single_focal_length_compatibility` — derives that 2D consistency forces
`(w/ws)·fx = (h/hs)·fy`, i.e., OpenCV's separate fx/fy are exactly representable
by a single OTI focal length F only when this constraint holds.

**Anti-Pattern Scan:** no issues. All five theorems are meaningful, non-proxy, and
non-vacuous.

**Verdict:** accepted

---

#### Distortion conversion theorems (9 theorems in DistortionConversion.lean)

**`whole_radial_polynomial_iff`:**
```lean
theorem whole_radial_polynomial_iff (k1 k2 k3 l1 l3 l5 F : ℝ) (hF : F ≠ 0) :
    (∀ r : ℝ, k1 * r^2 + k2 * r^4 + k3 * r^6 = l1 * (F*r)^2 + ...) ↔
    l1 = k1/F^2 ∧ l3 = k2/F^4 ∧ l5 = k3/F^6
```

**Hard Step (→):** Vandermonde-like specialization at r=1,2,3 produces a 3×3
system with columns 1,4,9 (from 1²,2²,3²). `nlinarith` closes after `field_simp`.
The coefficient uniqueness argument is correct.

**`all_distortion_conversions_iff`:** Bundles all 8 parameter conversions (6
radial + 2 tangential) into one iff. The strongest possible global distortion
theorem. Delegates to three sub-iffs.

**`radial_coefficients_imply_rational_factor_equality`:** Correctly identified as
one-way (→ only). The file explains why: different coefficient sets can yield the
same rational function. The one-way direction correctly follows from the coefficient
equality by `rw`. This is an honest limitation, not a weakened conclusion.

**Verdict:** accepted

---

#### `opencv_openlensio_full_pipeline_pixel_iff` (central theorem)

**Theorem Statement:**
```lean
theorem opencv_openlensio_full_pipeline_pixel_iff
    (k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1/F^2) ... (hq1 : q1 = p1/F^2) (hq2 : q2 = p2/F^2)
    (hF_eq : F = (w/ws)*fx) (hΔPx : ΔPx = (w/ws)*(cx - ws/2))
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hden : ∀ x' y' : ℝ, 1 + k4*(x'^2+y'^2) + ... ≠ 0) :
    (∀ x' y' : ℝ, [OpenCV pixel x] = [OpenLensIO pixel x]) ↔ ws/w = fx
```

**Plain English:** Given all parameter conversions, the full pixel x-outputs agree
for every normalized input iff `ws/w = fx`. The coefficient conversions alone are
not sufficient — the scale ratio is the exact additional condition.

**Parameter and Hypothesis Audit:**

| Name | Type / Role | Used? | Necessary? | Suspicious? | Notes |
|---|---|---|---|---|---|
| `hw, hws` | nonzero guards | yes | yes | no | field_simp needs these |
| `hF, hF_pos` | F nonzero/positive | yes | yes | no | hF for algebra; hF_pos for sqrt in RadialPipeline |
| `hp : p1≠0 ∨ p2≠0` | tangential nonzero | yes | yes | no | load-bearing for → direction; without it, scale is undetectable |
| `hden` | denominator nonzero | yes | yes | no | needed for field division |
| `hl1..hq2` | conversion hypotheses | yes | yes | no | the paper's claimed formulas |

**Conclusion Audit:**
- Conclusion strong enough: yes — full iff, not just sufficiency
- Not a proxy: yes — pixel equality IS the intended property
- Not test-shaped: yes — universal over all (x', y') : ℝ

**Proof Strategy:**
- First meaningful tactic: `constructor`
- → direction: `pixel_eq_implies_tangential_gap` (extracts gap term) → `tangential_gap_forces_scale` (closes to `ws/w = fx`)
- ← direction: delegates to `opencv_openlensio_full_pipeline_pixel_sufficiency`

**Hard Step (→):** `pixel_eq_implies_tangential_gap` uses `linear_combination`
with the radial ratio equality, two tangential simplifications, and the principal
offset cancellation. `tangential_gap_forces_scale` specializes at (1,1) and (1,−1)
for `p1≠0`, at (0,1) for `p2≠0`.

**Hard Step (←):** `opencv_openlensio_full_pipeline_pixel_sufficiency` derives
`ws = w·fx` from `hscale`, shows radial numerator and denominator agree at scaled
radii, then closes by `field_simp + ring`.

**Automation Review:**
- `linear_combination`: exposes the algebraic structure explicitly — not hidden
- `field_simp + ring`: appropriate for rational function identity after parameter substitution
- Hard step is recoverable: the `linear_combination` witness is explicit

**Anti-Pattern Scan:**

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Over-strong hypotheses | no | `hp` is load-bearing — without it, scale is undetectable from tangential terms | |
| Weakened conclusion | no | full iff | |
| Broad automation hiding hard step | no | `linear_combination` witness is explicit | |

**Verdict:** accepted

---

#### Mutation tests (MutationTests.lean — 24 theorems)

**Structure:** Layer 1 (forces degeneracy) + Layer 2 (closes to False) per wrong
formula, covering groups A (buggy ΔPx), B–C (wrong offset variants), D (F = fx),
E (inverted F), F.1–F.6 (wrong radial powers), G.1–G.4 (wrong tangential powers),
H.1–H.3 (coefficient swaps).

**Non-vacuity confirmation:** Section I contains two sanity examples:
- I.1: symbolic witness — correct principal-point formulas satisfy consistency
- I.2: numeric witness — w=2, ws=1, fx=3, cx=4 → F=6, ΔPx=7, verified by `ring`

Without these, every mutation theorem would be vacuously true. They are present
and correct.

**Verdict:** accepted

---

## Module Topology Review

```
MODULE TOPOLOGY REVIEW:
- Does each touched Lean file have one clear semantic responsibility: yes
- Did the task create one file per slice: no (files organized by semantic unit)
- Did the task create a monolithic file: no
- Are helper lemmas located near their stable API use: yes
  (PixelIffHelpers colocated with PixelIff in Pipeline/; private H1–H8 in NumericLiteralRoundtrip)
- Are private/local lemmas kept private or in intentional helper modules: yes
- Are public compatibility imports preserved: yes
  (PipelineEquivalence.lean is a clean re-export shim; PixelEquivalence re-exports as pipeline-form)
- Did import dependencies become broader than necessary: no
- Does the file layout make future proof repair easier: yes
```

No monolith risk. No oversplit risk. No file is named after a repair attempt,
slice number, or session.

---

## Forbidden Construct Check (Repo-Wide)

- `sorry`: **absent** — grep found 0 matches in source files
- `admit`: **absent** — 0 matches
- `set_option warn.sorry false`: **absent** — 0 matches
- Unauthorized `axiom`: **absent** — 0 matches
- Unauthorized `constant`: **absent** — 0 matches
- `unsafe`: **absent** — 0 matches
- `partial`: **absent** — 0 matches

Placeholder hygiene: no sorry replaced with axiom or constant. No warning
suppression directives in any file.

---

## Repository-Level Anti-Pattern Scan

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Statement laundering | no | | |
| Vacuity | no | Mutation I.1/I.2 sanity examples confirm satisfiability | |
| Weakened conclusion | no | all key theorems are full iff or full equality | |
| Over-strong hypotheses | no | all nonzero/positivity guards are load-bearing | |
| Unused hypotheses | minor | `tj` in decodeTransform_missing_rotation — structurally needed | low |
| Unreadable specification | no | | |
| Test-shaped theorems | no | all theorems are universally quantified | |
| Tactic soup | no | | |
| Broad automation hiding hard step | no | linear_combination exposes structure | |
| Algebra rewrite ping-pong | no | | |
| Misused `<;>` | no | `<;>` used correctly for parallel goal extension | |
| Runtime failure replacing proof | no | | |
| Verifier confusion | minor | IntegrationSmoke #eval — correctly scoped as smoke test | low |
| Documented α-equivalence | yes | deltaP/deltaC_characterisation — intentional, documented | low |
| Junk-value semantics | noted | angle_of_view_eq at F=0 — documented; caller-enforced | low |

---

## Honest Limitation Disclosures (not defects)

Two scope limitations are correctly documented in source comments:

1. **`ProjectionModel.lean`:** `projection_matrix_undistort_eq` proves offset
   cancellation only, not full Eq(3)/Eq(4) forward/inverse equivalence. The
   full equivalence requires the forward distortion model, deferred to OL-DEFER-03.

2. **`DistortionConversion.lean`:** `radial_coefficients_imply_rational_factor_equality`
   is one-way only. The file explains why (different coefficients can produce the
   same rational function). The stronger coefficient-level theorems are the
   primary results.

---

## Required Action

none — all proofs are accepted. Three low-severity notes for maintainer awareness:
1. `deltaP_characterisation`/`deltaC_characterisation` α-equivalence is documented
   in the code (VAC-01); consider adding a cross-reference comment if the paper
   equation numbering changes.
2. `angle_of_view_eq` junk-value at F=0 is benign; no action needed.
3. `IntegrationSmoke.lean` `#eval` results are not proofs; the file correctly
   scopes them as smoke tests.
