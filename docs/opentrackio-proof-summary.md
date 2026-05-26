# Formal Verification of Camera Metadata Interoperability for OpenTrackIO

---

## Abstract

This paper describes the formal verification work in the `opentrackio-proof` repository, which applies Lean 4 machine-checked proofs to three areas of the OpenTrackIO camera-tracking metadata ecosystem. The first area proves that the OpenCV-to-OpenTrackIO lens calibration parameter conversions described in a SMPTE RIS technical paper [OTI-CVX] are mathematically correct and uniquely determined — necessary, not merely sufficient — and that the full distortion pipelines of both systems are pixel-for-pixel equivalent under exactly the conditions the conversions require. The second area formalizes the Brown-Conrady distortion pipeline of the OpenLensIO v1.0.1 specification [OLENS] in exact real arithmetic and proves structural consistency between its two parameterizations. The third area verifies the OpenTrackIO JSON data model, establishing encode/decode roundtrip fidelity, decoder soundness with respect to type-carried structural invariants, and normalization idempotence. Together, the three areas cover approximately 100 public theorems, all proved using only standard Mathlib tactics over exact reals. This document describes what was proved, reproduces the central mathematical claims, explains how the theorem statements were derived from the source documents, and records the explicit scope limits that bound what can and cannot be concluded.

---

## 1. Introduction

Virtual production systems depend on accurate, interoperable exchange of camera metadata. A camera-tracking sample transmitted from a motion-capture system to an LED volume or compositing engine carries position, orientation, and lens parameters. If two implementations interpret the same data differently — because they disagree on coordinate conventions, sign choices, or coefficient scaling — the result is not typically a loud crash. It is a subtle geometric disagreement that manifests as misregistered virtual elements in a final frame. These disagreements are expensive to diagnose, and because each affected implementation may be internally consistent, ordinary unit tests may not surface them.

Formal verification addresses this class of problem at the mathematical level. It does not merely test whether an implementation behaves correctly on sample inputs; it proves that a precisely stated mathematical claim holds for all inputs in its domain. This is useful when the claim is about interoperability between two systems — that is, when the risk is not a single implementation failing but two otherwise-correct implementations disagreeing on meaning.

The OpenTrackIO ecosystem is an appropriate target for this approach. OpenTrackIO [OTI-CVX] is an SMPTE RIS open standard for camera-tracking metadata. OpenLensIO [OLENS] is a companion specification for lens distortion parameters. Both standards define data formats that independent software stacks will consume and render. Errors in coordinate convention or coefficient scaling produce incorrect imagery, and those errors are documented in the source literature: the SMPTE RIS conversion paper notes an earlier version contained a bug — a missing half-width centering term — that was geometrically inconsistent with the stated coordinate model.

This work formalizes the relevant mathematical claims in Lean 4, using Mathlib's noncomputable real-arithmetic infrastructure. All proofs are machine-checked by Lean's kernel. No custom axioms are introduced beyond the Lean 4 standard library. Proof tactics are restricted to `field_simp`, `ring`, `linarith`, `nlinarith`, `norm_num`, and standard structural combinators.

The remainder of this paper is organized as follows. Section 2 gives background on the mathematical content of the source documents. Section 3 covers the principal-point and distortion coefficient conversion proofs. Section 4 covers the full pipeline equivalence results and mutation tests. Section 5 covers the OpenLensIO semantic formalization. Section 6 covers the OpenTrackIO parser verification. Section 7 addresses how one can evaluate whether the theorem statements capture the right claims. Section 8 records explicit scope limits. Section 9 concludes.

---

## 2. Background

### 2.1 OpenCV and OpenTrackIO Coordinate Conventions

Camera calibration in OpenCV uses two distinct coordinate spaces [OTI-CVX]. Normalised (undistorted) coordinates `(x'', y'')` are scene-relative: they are obtained by dividing world-frame camera coordinates by the depth component `z`. Pixel coordinates `(u, v)` are then produced by:

```
u = fx * x'' + cx
v = fy * y'' + cy
```

where `fx`, `fy` are the focal lengths in pixels, and `cx`, `cy` are the pixel coordinates of the principal point measured from the **upper-left corner** of the image.

OpenTrackIO uses a different convention for the same geometric relationship. Normalised coordinates are mapped to screen coordinates `ε'_d` via:

```
ε'_x,d = F * x'' + ΔPx
```

and pixel coordinates are recovered as:

```
u = (w_shader / w) * ε'_x,d + w_shader / 2
```

where `F` is a single scalar focal length, `ΔPx` is the projection offset, `w_shader` is the sensor width in shader units, `w` is the sensor width in physical units, and the `+ w_shader/2` term reflects that the OpenTrackIO origin is at the **center** of the image [OTI-CVX].

The centering convention difference is not a minor notational choice. It means the two coordinate systems cannot be equated by simply matching coefficients name-by-name. The correct conversion must be derived by requiring that both systems assign the same pixel coordinate to every scene point.

### 2.2 Brown-Conrady Lens Distortion

The OpenLensIO specification [OLENS] defines lens undistortion using the Brown-Conrady model. Undistorted screen coordinates `ε_u` are related to distorted coordinates `ε_d` by:

```
ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP
```

where `ΔC` is the distortion center offset and `ΔP` is the perspective offset. The undistortion function `U` is:

```
U(ε) = R(r) * ε + T(ε)
```

where `r = |ε|` is the sensor radius, `R(r)` is the rational radial polynomial, and `T(ε)` is the Brown-Conrady tangential correction.

The radial polynomial is a degree-6 rational function in `r²`:

```
R(r) = (1 + k1*r² + k3*r⁴ + k5*r⁶) / (1 + k2*r² + k4*r⁴ + k6*r⁶)
```

Note the OpenLensIO coefficient convention: `k1, k3, k5` are numerator coefficients; `k2, k4, k6` are denominator coefficients. This alternating layout differs from the OpenCV convention, where `k1, k2, k3` are numerator and `k4, k5, k6` are denominator. This naming distinction must be tracked carefully when stating conversion theorems.

The tangential correction is:

```
T_x(ε) = 2*p1*ε_x*ε_y + p2*(r² + 2*ε_x²)
T_y(ε) = p1*(r² + 2*ε_y²) + 2*p2*ε_x*ε_y
```

The OpenLensIO specification defines two equivalent parameterizations of the same lens [OLENS]: a **projection-matrix form** (Equation 4) and a **FOV form** (Equation 10). Both are stated to be equivalent under the coordinate translation in Equation 13:

```
ε_d = ε'_d + ΔP
```

This equivalence is stated in prose but not proved in the specification. Formally establishing it is one of the primary results of the semantic verification effort.

---

## 3. Principal-Point and Distortion Coefficient Conversion Proofs

### 3.1 The Correctness Criterion

The conversion from OpenCV to OpenTrackIO is correct if and only if both systems assign the same pixel coordinate to every scene point. This consistency requirement for all `x''` takes the form:

```
fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2
```

The central mathematical question is: what values of `F` and `ΔPx` satisfy this equation for **all** `x''`? The equation is linear in `x''`, so it constrains both the slope and the intercept independently:

- **Slope:** `fx = (w_shader / w) * F`, which gives `F = (w / w_shader) * fx`
- **Intercept:** `cx = (w_shader / w) * ΔPx + w_shader / 2`, which gives `ΔPx = (w / w_shader) * (cx − w_shader / 2)`

This is the unique solution. There is no choice; the values are forced by the requirement that all scene points agree.

### 3.2 The Principal-Point Theorems

Five theorems are proved in `PrincipalPointConversion.lean`, all for real-valued parameters with nonzero image dimensions (`w ≠ 0`, `w_shader ≠ 0`).

**Theorem** `principal_point_conversion_necessary` — Uniqueness of the conversion:

```lean
theorem principal_point_conversion_necessary
    (w w_shader fx cx F ΔPx : ℝ)
    (hw : w ≠ 0) (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2) :
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2)
```

This theorem states that the consistency condition alone, for all `x''`, uniquely forces the published conversion formulas. The proof specializes at `x'' = 0` and `x'' = 1` to separate slope and intercept, then applies `field_simp` and `nlinarith` to derive the coefficient equations.

**Theorem** `principal_point_conversion_iff` — Necessary and sufficient:

```lean
(∀ x'' : ℝ, fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2)
↔
F = (w / w_shader) * fx  ∧  ΔPx = (w / w_shader) * (cx - w_shader / 2)
```

This is the strongest possible form: the consistency condition holds for all scene points if and only if the parameters take exactly the published values.

**Theorem** `principal_point_conversion_2d_iff` — Full 2D camera-model theorem:

```lean
(∀ x'' y'' : ℝ,
    fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2  ∧
    fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2)
↔
F = (w / w_shader) * fx  ∧  ΔPx = (w / w_shader) * (cx - w_shader / 2)  ∧
F = (h / h_shader) * fy  ∧  ΔPy = (h / h_shader) * (cy - h_shader / 2)
```

This theorem incorporates the full 2D geometry. The x-axis and y-axis conditions are independent linear problems, each forcing the same scalar `F`. This leads directly to a compatibility constraint:

**Theorem** `single_focal_length_compatibility`:

```
(w / w_shader) * fx = (h / h_shader) * fy
```

This states that an OpenCV calibration, which carries separate `fx` and `fy`, is representable by a single OpenTrackIO scalar `F` only when the above equality holds. When it fails, no single `F` can satisfy both axes. This is a useful diagnostic: it makes explicit the assumption implicit in the SMPTE RIS paper that OpenCV's `fx` and `fy` are related by the sensor aspect ratio [OTI-CVX].

**Theorem** `buggy_principal_point_conversion_inconsistent` — Regression guard:

```lean
-- Given: ΔPx = (w / w_shader) * cx  (the earlier erroneous formula)
-- Conclusion: False
```

The earlier version of the SMPTE RIS paper used `ΔPx = (w / w_shader) * cx`, omitting the `−w_shader/2` centering term. This theorem proves that this formula is not merely imprecise — it is mathematically inconsistent with the consistency condition under any nonzero image dimensions. The proof shows that the buggy formula and the correct formula together force `w_shader = 0`, contradicting the nonzero hypothesis.

### 3.3 Distortion Coefficient Conversion

OpenCV distortion is expressed in normalised coordinates `(x', y')` with radius `r`. OpenTrackIO distortion is expressed in screen coordinates `(ε_x, ε_y) = (F*x', F*y')` with radius `r_u = F*r`. For the two systems to produce identical distortion corrections, their polynomial contributions must agree at every point. This requirement for radial distortion at degree `2n` takes the form:

```
∀ r, k * r^(2n) = l * (F * r)^(2n)
```

which forces `l = k / F^(2n)`. For tangential distortion, the cross-term consistency condition

```
∀ x' y', p1 * x' * y' = q1 * (F * x') * (F * y')
```

forces `q1 = p1 / F²`, and similarly `q2 = p2 / F²`.

The three per-term theorems `radial_distortion_conversion`, `tangential_q1_conversion`, and `tangential_q2_conversion` prove these individually.

The key strength of the formalization lies in the **whole-polynomial** theorems. Rather than assuming terms correspond individually, these theorems derive coefficient uniqueness from polynomial identity:

**Theorem** `whole_radial_polynomial_iff`:

```lean
(∀ r : ℝ,
    k1 * r² + k2 * r⁴ + k3 * r⁶ =
    l1 * (F*r)² + l3 * (F*r)⁴ + l5 * (F*r)⁶)
↔
l1 = k1/F²  ∧  l3 = k2/F⁴  ∧  l5 = k3/F⁶
```

The backward (sufficiency) direction is straightforward substitution. The forward (necessity) direction is more subtle: the hypothesis gives a single polynomial equation, not three separate ones. The proof specializes at `r = 1, 2, 3` and solves the resulting 3×3 Vandermonde-like linear system. The key fact is that the coefficient matrix — derived from evaluating `r², r⁴, r⁶` at `r = 1, 2, 3` — has a nonzero determinant (values `1, 1, 1; 1, 4, 16; 1, 9, 81` after scaling), which `nlinarith` closes. This is a genuine polynomial coefficient extraction, not a pointwise consistency check.

**Theorem** `all_distortion_conversions_iff` composes all eight conversions into a single biconditional:

```
(radial numerator polynomials agree for all r)  ∧
(radial denominator polynomials agree for all r)  ∧
(2D tangential vector field agrees for all x', y')
↔
l1 = k1/F²  ∧  l3 = k2/F⁴  ∧  l5 = k3/F⁶  ∧
l2 = k4/F²  ∧  l4 = k5/F⁴  ∧  l6 = k6/F⁶  ∧
q1 = p1/F²  ∧  q2 = p2/F²
```

This is the central result for the distortion conversion: all eight conversions are jointly necessary and sufficient for full polynomial agreement. A consequence, proved separately as `radial_coefficients_imply_rational_factor_equality`, is that the rational radial scale factors of both systems agree pointwise once the coefficient conversions hold.

---

## 4. Full Pipeline Equivalence and Mutation Tests

### 4.1 Pixel Coordinate Equivalence

With principal-point and distortion conversions established, the natural next question is whether the full pipelines — from normalised input coordinates to pixel output — agree. Two theorems address this.

**Theorem** `opencv_openlensio_full_pipeline_pixel_sufficiency` establishes sufficiency: given all coefficient conversions and the condition `w_shader / w = fx`, the x-pixel outputs of the OpenCV and OpenTrackIO pipelines agree for all normalised inputs.

**Theorem** `opencv_openlensio_full_pipeline_pixel_iff` establishes the biconditional (requiring `p1 ≠ 0 ∨ p2 ≠ 0` to make the tangential components non-trivially constrained):

Given all distortion coefficient conversions and at least one nonzero tangential coefficient:

```
full x-pixel outputs agree for all normalised inputs  ↔  w_shader / w = fx
```

The tangential assumption matters. The radial components agree after conversion regardless of the aspect-ratio condition; it is the tangential components that introduce the factor `(w_shader/w − fx)`, which vanishes only when those are equal. Without nonzero tangential coefficients, the condition `w_shader/w = fx` is not entailed by pixel agreement.

This result connects formally to the SMPTE RIS derivation [OTI-CVX]: both systems agree at the pixel level precisely under the same condition that the paper uses to relate `F` to `fx`, namely that the physical sensor and shader aspect ratios are consistent.

### 4.2 Mutation Tests

Forty mutation-test theorems in `MutationTests.lean` address a natural adversarial question: are the published formulas the only ones that work, or are there plausible alternatives? The answer is no — every tested variant fails in a specific, provable way.

Variants tested fall into three categories:

1. **Wrong offset form for principal-point conversion.** Three pairs cover: the buggy formula `ΔPx = (w/w_shader) * cx` (already addressed as `buggy_principal_point_conversion_inconsistent`), sign-swapped variants, and other offset alternatives. Each is shown either inconsistent with the consistency condition or degenerate (forcing special coefficient relationships).

2. **Wrong focal-length scaling power.** For each of the eight distortion coefficients `l1–l6, q1–q2`, the correct scaling is `1/F^(2n)` for the appropriate degree. Variants using the wrong power (e.g., `l1 = k1/F⁴` instead of `k1/F²`) are shown to force the degenerate condition `F^n = F^m` for distinct `n, m`, which holds only for `F = 0` or `F = 1`.

3. **Coefficient swaps.** Pairing `l1` with `k2` rather than `k1`, or `q1` with `p2` rather than `p1`, forces those distinct coefficients to be equal — an almost-always-false arithmetic coincidence that the system rejects as a universally satisfied condition.

These 40 theorems collectively establish that the conversion formulas are not just one possible choice among many consistent options; they are the unique correct choice, with every known wrong variant provably failing.

---

## 5. OpenLensIO Semantic Formalization

### 5.1 Scope and Motivation

Parser correctness does not imply semantic correctness. Two implementations can decode identical byte sequences to identical numeric values and still render different images because they disagree on coordinate frames or composition order within the lens pipeline. This is the class of error that semantic formalization targets.

The OpenLensIO v1.0.1 specification [OLENS] defines the Brown-Conrady undistortion pipeline over a sequence of coordinate-space transformations. The formal model in `openlensio_semantics/` encodes each step as a Lean 4 function over exact reals (`ℝ`) and proves structural invariants connecting them.

### 5.2 The Formal Model

The coordinate pipeline modeled is:

```
world coordinates
  → camera-frame normalised coordinates  (divide by z)
  → screen coordinates                   (multiply by F, add ΔP)
  → distortion-center frame              (subtract ΔC)
  → apply Brown-Conrady undistortion U
  → add back ΔC + ΔP
  → sensor plane (mm, origin at center)
  → shader/texture coordinates (pixel units)
```

The Lean definitions are:

- `RadialCoefficients` — the six-coefficient record `⟨k1, k2, k3, k4, k5, k6⟩` in OpenLensIO alternating layout (numerator: `k1, k3, k5`; denominator: `k2, k4, k6`)
- `TangentialCoefficients` — `⟨p1, p2⟩`
- `radialTerm r` — evaluates `R(r)` as the rational polynomial, with a `denominatorNonzero` domain hypothesis
- `undistortPoint ε` — the full `U(ε) = R(r)·ε + T(ε)` computation
- `undistortFromDistorted` — projection-matrix form (Equation 4 of [OLENS])
- `fovUndistortFromDistorted` — FOV form (Equation 10 of [OLENS])

All are defined over `ℝ` using Mathlib. The executable Float layer in `ExecutableSemanticOracle.lean` is separate and not formally connected to these definitions.

### 5.3 Identity and Degenerate-Input Theorems

**Theorem** `brown_conrady_zero_identity`:

```
All coefficients zero → undistortPoint ε = ε
```

This is the basic sanity check: a pinhole lens (no distortion) is the identity map. The proof chains through `radial_zero_coefficients_identity` (R(r) = 1 when k1=k3=k5=k2=k4=k6=0) and `tangential_zero_coefficients_identity` (T(ε) = 0 when p1=p2=0).

**Theorem** `radial_denominator_nonzero_zero_coeffs`:

```
k2 = 0 ∧ k4 = 0 ∧ k6 = 0 → denominator = 1  (hence ≠ 0)
```

This establishes that the `denominatorNonzero` predicate is satisfiable by the common case of zero denominator coefficients. The specification [OLENS] does not state conditions under which the denominator is guaranteed nonzero; the formal model makes this a per-point domain requirement, forcing any implementation to reason about it explicitly.

### 5.4 FOV and Projection Form Consistency

The central structural result in the semantic formalization connects the projection-matrix form (Equation 4 of [OLENS]) and the FOV form (Equation 10 of [OLENS]) through the coordinate translation of Equation 13.

Equation 13 of [OLENS] states:

```
ε_d = ε'_d + ΔP
```

In the projection-matrix form, undistortion is applied to `ε_d − ΔC − ΔP`. Substituting Equation 13:

```
ε_d − ΔC − ΔP = (ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC
```

The ΔP terms cancel, so both forms apply `U` to the same distortion-centered coordinate `ε'_d − ΔC`. This is not merely convenient algebra; it is the load-bearing sign-convention result. An implementation that uses the wrong sign for ΔP in Equation 13 produces incorrect output for any lens with nonzero ΔP, and the error is not detectable by ordinary unit tests without a calibration target designed to stress that term.

**Theorem** `distortion_center_translation_commutes` formalizes this cancellation.

**Theorem** `fov_undistort_eq`:

```
undistortFromDistorted(ε'_d + ΔP) = fovUndistortFromDistorted(ε'_d) + ΔP
```

This is the full consistency theorem: the projection-matrix undistortion of a distorted point equals the FOV undistortion of the corresponding FOV-convention coordinate, plus the ΔP offset. The proof requires a congruence lemma that bridges two formally distinct but propositionally equal domain hypotheses — the two pipeline forms carry differently-typed domain evidence for the same mathematical condition on the radial denominator.

### 5.5 Coordinate Roundtrips and Angle-of-View

**Theorems** `pixel_metric_roundtrip` and `image_texture_coordinate_roundtrip` prove that the metric-to-shader and shader-to-metric conversions are exact mutual inverses under the positivity conditions satisfied by any physical sensor.

**Theorem** `angle_of_view_eq` proves the trigonometric relationship stated in Equation 18 of [OLENS]:

```
tan(α/2) = r_u / F
```

where `r_u` is the undistorted sensor radius and `F` is the focal length. This connects the formal definition of angle of view to the specification's stated formula.

**Theorem** `semanticExtraction_sound` proves that the lens parameter extraction function produces a result satisfying the `ValidLensSemantics` predicate, which requires `0 < focalLength`. This is the formal bridge between raw data and the semantic layer.

### 5.6 Injectivity

Injectivity of the undistortion map `U` is partially established in three regimes:

- `undistortPoint_injective_zero_tangential` — on-circle injectivity when `p1 = p2 = 0` and `R(r) ≠ 0`
- `undistortPoint_injective_pure_radial` — global injectivity for `p = 0` given a caller-supplied scale-injectivity hypothesis
- `undistortPoint_injective_on_circle_tangential` — on-circle injectivity with full tangential terms, under a nonzero linear-system determinant hypothesis

A conditional left-inverse theorem `radialDescale_left_inverse_zero_tangential` establishes `D(r, U(ε)) = ε` for `p = 0`, where `r = sensorRadius(ε)` must be supplied by the caller. This captures an important structural fact: the specification [OLENS] defines forward distortion `D = U⁻¹` but prescribes numerical iteration for computing it, because no closed-form inverse exists for the general model. The conditional left inverse, requiring `r` as an external parameter, is the closest formal statement achievable without the iterative computation or Implicit Function Theorem machinery.

---

## 6. OpenTrackIO Parser Verification

### 6.1 Design Philosophy: Type-Carried Invariants

The parser verification project models the OpenTrackIO v1.0.1 data model over a `JsonValue` abstract syntax tree. Rather than proving predicates separately about decoded values, the model embeds protocol invariants directly into types:

- `PositiveRational` carries proofs `num_pos : 0 < num` and `den_pos : 0 < den`
- `NonemptyArray T` carries a proof that its list is nonempty
- `NonemptyString` carries a proof that its string is not `""`
- Protocol version digits have type `Fin 10`, making out-of-range digits unconstructible

This design means decoders serve as gatekeepers. A value of type `NonemptyArray T` that has passed through a verified decoder provably has a nonempty list — the proof is stored in the value itself. Later theorems about decoded samples can appeal to these type-level facts rather than re-inspecting decoder logic.

### 6.2 Encode/Decode Roundtrip

The strongest theorem in the parser verification is:

**Theorem** `encodeSample_roundtrip`:

```lean
theorem encodeSample_roundtrip (s : Sample) :
    decodeSample (encodeSample s) = .ok s
```

For any sample constructible in the formal model, encoding it to JSON and decoding the result returns the original sample. This theorem directly exercises both the real encoder and the real decoder and proves their agreement, not a hand-written predicate. Several failure modes are excluded by the theorem:

- A constant encoder fails for populated samples (decoded values would disagree on fields)
- A decoder that ignores fields fails to recover the original value
- A key-name mismatch — encoding `pinholeFocalLength` but decoding `focalLength`, for instance — breaks the roundtrip

The sub-component roundtrip theorems (`encodeProtocol_roundtrip`, `encodeTransform_roundtrip`, `encodeLens_roundtrip`, and so on) build toward this result hierarchically, with each level of the encoding proven before the next.

### 6.3 Decoder Soundness

Five composed decoder soundness theorems establish that decoded samples preserve structural invariants:

- `decodeSample_transforms_sound` — transform arrays are nonempty
- `decodeSample_protocol_sound` — protocol version satisfies `ValidVersion`
- `decodeSample_lens_encoders_sound` — lens encoder group has at least one of focus, iris, or zoom present (`FizOptions.anyPresent`)
- `decodeSample_static_duration_sound` — static duration rational is positive
- `decodeSample_static_camera_sound` — camera frame-rate rational is positive

These are not vacuous: each depends on decoder logic that enforces the invariant from the JSON input.

Five error-correctness theorems prove that specific malformed inputs produce the expected error tags: missing `protocol.name`, missing `protocol.version`, missing transform `translation`, missing transform `rotation`, and missing rational `num`. These establish that the decoder does not silently accept required-field failures.

### 6.4 Normalization

**Theorem** `sampleNormalize_idempotent`:

```
sampleNormalize ∘ sampleNormalize = sampleNormalize
```

A second pass of normalization changes nothing.

**Theorem** `normalization_under_wellFormed`:

```
WellFormedSampleJson j  ∧  decodeSample j = .ok s  →
sampleNormalize j = encodeSample s
```

Normalization of a well-formed input that decodes to `s` produces the same JSON as encoding `s` from scratch. This characterizes normalization as a canonical-form operation: it collapses any equivalent representation of the same semantic content to a single canonical form.

### 6.5 Differential Testing Oracle

The parser verification is connected to practical engineering through the `battery-tester` differential harness. The harness runs a Python camdkit adapter, a Mo-Sys C++ adapter, and the Lean oracle against the same canonical JSON fixtures, then compares 18 fields field-by-field. The Lean oracle operates on the parsed JSON AST rather than raw bytes — Python parses the bytes, then hands the structured data to the Lean model. This boundary is intentional: it allows the Lean oracle to provide value immediately as a semantic reference, without requiring byte-level JSON verification.

A concrete bug was found through this harness: the Python camdkit adapter used the key `lens.focalLength`, while the OpenTrackIO protocol specifies `lens.pinholeFocalLength`. The Lean model uses the normative key and independently confirmed which implementation was incorrect.

---

## 7. Evaluating the Claims: How Do We Know the Theorems Are Right?

A reader familiar with formal methods will want to assess not just whether the proofs are valid, but whether the theorem statements capture the intended properties. This section addresses that question for each area.

### 7.1 Conversion Theorems

The theorem statements for principal-point and distortion coefficient conversion are derived from first principles, not from the SMPTE RIS paper [OTI-CVX] directly. The paper states the conversion formulas; the theorems derive them from the consistency condition. This derivation structure makes the theorems largely self-auditing: anyone who agrees on the coordinate conventions (OpenCV uses upper-left-origin pixels; OpenTrackIO uses center-origin pixels) can verify that the consistency equation is correct, and the necessity derivation follows from standard linear algebra.

The bugs caught — the missing `−w_shader/2` centering term in the principal-point conversion — further validate the approach: the formal derivation detected an error in the original source document.

The distortion conversion theorems are grounded similarly. The coefficient scaling laws `l = k / F^(2n)` are derived from the requirement that both systems evaluate the same polynomial distortion at the same point, just expressed in different coordinate scales (`r` vs. `F*r`). The Vandermonde-based necessity proof shows that if you only know the full polynomial agrees, you can still uniquely extract the individual coefficients — which is the appropriate level of generality given that a renderer sees a full polynomial, not individual terms.

### 7.2 Semantic Formalization

The OpenLensIO specification [OLENS] states the Brown-Conrady model in equations. The Lean definitions translate those equations into functions. The primary auditing challenge is whether the functions match the equations, particularly for the coordinate-frame conventions.

Several specification ambiguities were discovered during formalization and catalogued in `docs/specification-questions.md`. Ten remain open; five were resolved. The most consequential resolved question was the ΔP sign convention: Equation 13 of [OLENS] states `ε_d = ε'_d + ΔP`, and this sign choice is load-bearing for the `fov_undistort_eq` theorem. The specification states it consistently across Equation 13 and the inline text near Equation 10. The formal proof confirms that only this sign makes the FOV and projection forms equivalent.

The domain predicate `denominatorNonzero` is another place where the formal model makes explicit something the specification leaves implicit. The specification [OLENS] defines the radial polynomial without discussing its denominator's domain. Lean's type system forces an explicit treatment: any function that divides by the denominator must carry a proof of nonzero denominator, and that proof requirement propagates upward to every call site. This is a feature, not a limitation: it makes the domain assumption visible and auditable.

### 7.3 Parser Verification

The encode/decode roundtrip theorem is the most self-evidently correct claim: encode then decode should return the original. Its correctness as a theorem statement does not require domain knowledge of OpenTrackIO; any reader can verify it is the right property to prove.

The decoder soundness theorems require matching the Lean invariant predicates to OpenTrackIO schema requirements. For example, `FizOptions.anyPresent` corresponds to the OpenTrackIO requirement that lens encoder groups contain at least one of focus, iris, or zoom. Readers evaluating these theorems should compare the predicates to the OpenTrackIO v1.0.1 schema.

---

## 8. Scope and Limitations

### 8.1 Conversion Proofs

The full pipeline equivalence theorem is proved for the x-pixel coordinate only. The y-coordinate follows by a symmetric argument (swapping `p1 ↔ p2` and using `F = (h/h_shader) * fy`), which is argued informally in `docs/limitations.md` but not formally proved. No joint 2D pixel-equivalence theorem is stated.

All proofs carry a `denominatorNonzero` hypothesis as a free precondition. Bounds on coefficients that guarantee this over a working radius range are not proved. The pure-radial case (`p1 = p2 = 0`) is not characterized by the pipeline iff theorem because the tangential terms that reveal the scale discrepancy vanish.

### 8.2 Semantic Formalization

Forward distortion `D = U⁻¹` is not formalized. The specification [OLENS] prescribes numerical iteration for the general Brown-Conrady model; no closed-form formula exists. The conditional left inverse `radialDescale_left_inverse_zero_tangential` (for `p = 0`) is the closest available result, but it requires the caller to supply the input radius `r`, which is not recoverable from `U(ε)` alone without inverting the radial scale — the very operation that requires iteration.

Global injectivity with full tangential coefficients is not proved. The on-circle result `undistortPoint_injective_on_circle_tangential` requires a nonzero determinant hypothesis that is not derived from coefficient bounds.

The overscan equations (Equations 8 and 15 of [OLENS]) drop ΔC and ΔP offsets asymmetrically between the two forms without explanation. No overscan theorems are attempted pending resolution of this ambiguity.

The executable Float layer (`ExecutableSemanticOracle.lean`) is not formally connected to the exact-real definitions. No error-bound theorem is proved. The Float layer uses an absolute tolerance of `1e-10` for domain checking, while the exact-real predicate requires strict inequality. The separation is intentional.

### 8.3 Parser Verification

The model operates on an already-parsed `JsonValue` AST. Byte-level JSON parsing is not verified. Numeric upper bounds, regex-constrained fields (UUID URNs, PTP identities), and maximum string lengths are not formalized. Duplicate-key behavior is handled by a `WellFormedSampleJson` predicate, not by the decoder directly.

`WellFormedSampleJson(encodeSample s)` — that encoders produce well-formed JSON — is not proved due to a module boundary issue.

### 8.4 Cross-Cutting

The three proof areas — conversion, semantics, and parser — are proved independently. No end-to-end theorem connects a parsed OpenTrackIO sample to a semantically correct pixel output. Building that connection would require a domain validation layer linking the parsed field values to the semantic model's preconditions.

---

## 9. Conclusion

This work applies Lean 4 machine-checked proof to three distinct but related mathematical properties of the OpenTrackIO ecosystem. The conversion proofs establish that the formulas in [OTI-CVX] are uniquely forced by coordinate-system consistency, ruling out alternatives through both necessity proofs and 40 explicit mutation tests. The semantic formalization establishes that the Brown-Conrady pipeline defined in [OLENS] is internally consistent — that its two characterizations, projection-matrix form and FOV form, agree under the coordinate translation specified in Equation 13 — and that the critical sign convention is load-bearing. The parser verification establishes encode/decode fidelity and structural invariant preservation for the OpenTrackIO v1.0.1 data model.

None of these results were previously machine-checked. The conversion proof detected a bug in an earlier version of [OTI-CVX] — the missing `−w_shader/2` centering term. Formalization of the semantic pipeline surfaced 17 specification questions across the three proof areas (catalogued in `docs/specification-questions.md`), including an unexplained asymmetry in the OpenLensIO overscan equations between Equations 8 and 15. The differential testing harness exposed a key-name discrepancy between a production Python adapter and the normative schema: the adapter read `lens.focalLength` while the OpenTrackIO protocol specifies `lens.pinholeFocalLength`; the Lean oracle independently confirmed which was correct. These are the payoffs that formal methods delivers over prose reading and ordinary testing: it converts specification claims into executable, auditable, machine-verified statements, and surfaces the assumptions those claims require.

The work is deliberately bounded. What is proved is stated precisely, and what is not proved is stated explicitly. The most significant open item is an end-to-end theorem connecting parsed data to pixel output, which requires the domain validation layer not yet present in the repository. That work would substantially strengthen the interoperability guarantee by closing the gap between the parser, semantic, and conversion results.

Genuine specification gaps surfaced during formalization are catalogued in `docs/specification-questions.md`. Three are directly verifiable against the OpenLensIO PDF. First, the denominator of the radial polynomial R (Equation 17 of [OLENS]) can be zero for pathological coefficient values; the specification is silent on any domain restriction. Second, the overscan equations are asymmetric in a way the specification does not explain: Equation 4 (projection, no overscan) adds both ΔC and ΔP after U, while Equation 8 (projection, with overscan) adds neither; Equation 15 (FOV with overscan) adds ΔC but not ΔP. The specification states the two forms "can generate equivalent renders" but does not prove it. Third, the specification does not state or prove any invertibility or continuity property of U. A fourth item — that computing forward distortion D requires iterative numerical methods — is acknowledged explicitly in Equation 11 of [OLENS], making it a proof scope limitation rather than an open specification question. The file `docs/specification-questions.md` also records proof-architecture concerns (such as the Float-to-exact-real bridge) under the same numbering scheme; readers should distinguish those from genuine specification ambiguities.

---

## References

**[OTI-CVX]** "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters." SMPTE Rapid Industry Solutions (RIS), corrected 2025-09-02. Available in this repository as `docs/OpenCV_to_OpenTrackIO.pdf`.

**[OLENS]** *OpenLensIO Lens Model Version 1.0.0/1.0.1 Specification.* Available in this repository as `docs/OpenLensIO_v1-0-1.pdf`. Note: the PDF cover page reads "Version 1.0.0" (17 February 2025); the filename suggests 1.0.1. The version discrepancy should be confirmed against the authoritative source.

**[LEAN4]** Leonardo de Moura and Sebastian Ullrich. "The Lean 4 Theorem Prover and Programming Language." In *Automated Deduction — CADE 28*, 2021.

**[MATHLIB]** The Mathlib Community. "The Lean 4 Mathematical Library." Available at https://github.com/leanprover-community/mathlib4.
