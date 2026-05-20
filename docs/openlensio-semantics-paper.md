# Executable Semantics for OpenLensIO: Formal Verification of Camera-Model Interoperability

**Mark Stalzer**
*opentrackio-proof project*

---

## Abstract

Parser correctness is not semantic correctness. Two implementations can decode identical byte sequences to identical numeric values and still render different images, because the coordinate systems and composition order of their lens models differ. This paper describes a Lean 4 formal verification campaign that moves beyond parser roundtrip proofs into executable camera-model semantics for the OpenLensIO lens model. We formalize the Brown-Conrady distortion pipeline, prove structural consistency theorems connecting the projection and FOV characterizations, and build an executable semantic oracle suitable for differential testing against reference implementations. A central finding of the campaign is that the OpenLensIO tangential distortion model and the OpenCV tangential distortion model operate in different coordinate frames: coefficient equality does not imply semantic equivalence, and interoperability must be established compositionally. We describe the proof architecture, the semantic ambiguities discovered in the specification, the vacuity audit discipline applied to the proof campaign, and the explicit boundaries of what has and has not been verified.

---

## 1. Introduction

The OpenTrackIO standard specifies a JSON protocol for camera tracking metadata in virtual production. A previous verification campaign established parser correctness for the OpenTrackIO format: it proved that the encoder and decoder are mutual inverses, that the decoder is sound with respect to a structural invariant predicate, and that semantic extraction from decoded data is sound with respect to a minimal validity predicate [prior work]. Those results are useful. But they answer the wrong question for interoperability.

Interoperability at the data level means that two systems agree on numeric values. Interoperability at the semantic level means that those numeric values, when consumed by a camera model, produce the same geometric result. The gap between these two properties is where rendering disagreements live in practice.

This campaign addresses the semantic level. We formalize the OpenLensIO v1.0.1 lens model in Lean 4, prove structural correctness theorems about its distortion and projection pipeline, build an executable Float oracle that can be tested against external implementations, and apply a systematic vacuity audit to ensure the formal results are not technically correct but semantically empty. The campaign spans 11 Lean source files and 14 public theorems, plus a Python differential testing harness.

---

## 2. Why Semantic Interoperability Matters

Consider two implementations that both decode the OpenLensIO tangential distortion coefficients p1 and p2 correctly. They agree on the values. But if one implementation feeds those coefficients a coordinate vector centered at the distortion center while the other feeds it a vector centered at the image principal point, they will apply a different correction at every pixel. The images will disagree. The disagreement is not a parsing bug. It is a coordinate-frame semantic bug.

This is not a hypothetical concern. The OpenCV lens model and the OpenLensIO lens model both use Brown-Conrady tangential distortion with coefficients named p1 and p2. Their formulas look similar. But OpenLensIO specifies that undistortion is applied to the coordinate `ε_d − ΔC − ΔP`, where ΔC is the distortion center offset and ΔP is the perspective offset. The tangential correction is therefore evaluated in the distortion-center frame. OpenCV's coordinate convention is different. A camera tracker that exports OpenLensIO coefficients and a renderer that imports them as OpenCV coefficients will produce different renders even when both sides implement their respective specifications exactly.

Detecting and preventing this kind of disagreement is the motivation for a semantic verification campaign. Parser tests cannot catch it. Unit tests on isolated functions may not catch it if both implementations are tested against their own internal conventions. The only reliable approach is to formalize what the specification actually says the pipeline should compute, then verify implementations against that formal model.

---

## 3. From Parser Correctness to Camera Semantics

The prior campaign proved that the parser and encoder are inverses, and that the decoder produces structurally valid data. These results establish a solid foundation: you can trust that data written in OpenTrackIO format can be read back accurately. What they do not establish is any claim about what happens after the data is read.

Camera-model semantics involves a chain of coordinate-space transformations:

```
world coordinates
  → camera-frame normalized coordinates (divide by z_p)
  → multiply by focal length F, add perspective offset ΔP
  → distortion-center frame (subtract ΔC)
  → apply Brown-Conrady undistortion U
  → add back ΔC + ΔP
  → sensor plane (mm units, origin at center)
  → shader/texture coordinates (pixel units)
```

Each step can introduce a semantic disagreement if implementations interpret an offset in the wrong direction, apply a transformation in the wrong order, or use coordinates from the wrong frame. The formal verification campaign makes each of these steps explicit, proves that the definitions implement what the specification says, and proves structural invariants that connect the steps.

The key semantic shift is from asking "does the decoder produce the right struct?" to asking "does the struct, when consumed by the camera model, produce the right coordinates?" This is a harder question, and it requires a different kind of formal argument.

---

## 4. Coordinate Systems and Semantic Ambiguity

Formalizing the OpenLensIO model required resolving several semantic ambiguities in the specification. Most of these are genuine interoperability hazards, not notation preferences.

**The ΔP sign ambiguity.** The specification contains an inline-text statement near Equation 10 claiming `ε'_d = ε_d + ΔP`, but Equation 13 elsewhere states `ε_d = ε'_d + ΔP`, which implies the opposite sign. Only one can be correct. Algebraic consistency with the rest of the model — specifically, that the FOV-form undistortion and the projection-matrix-form undistortion must feed U the same argument — confirms Equation 13 is authoritative and the inline text is a typo. The campaign registers this as an explicit load-bearing assumption. Any implementation that uses the opposite sign will produce incorrect results for lenses with nonzero ΔP.

**The distortion center frame.** OpenLensIO Equation 4 specifies that undistortion U is applied to the shifted coordinate `ε_d − ΔC − ΔP`. The tangential correction inside U therefore uses a radius r computed from this shifted point, not from the original image-plane coordinate. An implementation that computes r from the unshifted point and then applies the tangential correction will produce a subtly wrong result that may be difficult to detect without a calibration target with large tangential distortion.

**The rational radial polynomial's denominator.** The radial distortion factor R in OpenLensIO is a rational polynomial: both numerator and denominator are degree-6 polynomials in r². This differs from simpler polynomial models. The denominator can in principle be zero for pathological coefficient values, even though well-calibrated lenses will not produce such coefficients. The specification is silent on what implementations should do if the denominator is zero. The formal model resolves this explicitly: `denominatorNonzero` is a per-point domain predicate that callers must supply as a proof, making the failure mode impossible to ignore.

**The FOV versus projection characterizations.** OpenLensIO defines two mathematically equivalent ways to parameterize a lens: the projection matrix characterization (with perspective offset ΔP in the image plane) and the FOV characterization (without ΔP, using coordinates centered on the optical axis). The two characterizations are related by the ΔP translation: the projection form output is the FOV form output plus ΔP. The specification states this equivalence but does not prove it. One goal of the campaign was to formally verify this connection.

**The overscan offset inconsistency.** The specification's overscan equations (Equations 8 and 15) drop offset terms asymmetrically: the projection overscan form omits both ΔC and ΔP from the output; the FOV overscan form adds back ΔC but not ΔP. The paper does not explain this asymmetry. The campaign registers this as an unresolved ambiguity and defers overscan proofs.

---

## 5. Executable Semantic Modeling

Rather than proving isolated lemmas about abstract properties, the campaign formalizes the complete OpenLensIO semantic pipeline as Lean 4 functions and then proves theorems about those functions. This matters for two reasons. First, theorems about concrete functions can be tested against external implementations. Second, it forces all ambiguities in the specification to be resolved: a function that actually computes something cannot leave coordinate frames or signs unspecified.

The core definitions include `sensorRadius`, `radialTerm`, `undistortX`, `undistortY`, `undistortPoint`, `undistortFromDistorted`, `fovUndistortFromDistorted`, `toShaderCoords`, `fromShaderCoords`, `angleOfView`, and `fovAngleFromWidth`. These are all defined over exact real numbers (ℝ) using Mathlib's noncomputable function infrastructure. The exact-real layer is the one that carries formal proofs.

Alongside the exact-real layer, the campaign also produces an executable Float oracle in `ExecutableSemanticOracle.lean`. This file defines Float-valued versions of every semantic function — `undistortPoint_float`, `undistortFromDistorted_float`, `fovUndistortFromDistorted_float`, and so on. The Float oracle is not proved correct. It is infrastructure for differential testing. A Python reference oracle implementing the same formulas independently is tested against hand-computed expected values (7 fixtures covering the identity case, barrel distortion, pincushion distortion, the zero-origin boundary case, tangential distortion, domain failure at a near-zero denominator, and a full Equation 4 pipeline case). The Python oracle passes all 7 fixtures. This gives confidence that the Float oracle and Python oracle agree on the mathematical formulas, without claiming formal correctness of either.

The separation between the exact-real layer and the Float layer is explicit and enforced by design. The `ExecutableSemanticOracle.lean` file opens with a prominent warning: the Float functions are approximations that are not verified against the exact-real definitions. There is no bridging theorem connecting Float and ℝ semantics, and writing one would require IEEE 754 rounding error bounds that are out of scope for this campaign.

---

## 6. Key Verification Results

The 14 public theorems in the campaign fall into several categories.

**Zero-distortion identity.** The most fundamental property of a distortion model is that it should do nothing when all distortion coefficients are zero. The campaign proves `brown_conrady_zero_identity`: with all six radial coefficients and both tangential coefficients set to zero, `undistortPoint` returns its input unchanged. The proof chains through two helper lemmas: first `radial_zero_coefficients_identity` (the radial factor R reduces to 1 when all k-coefficients are zero), then `tangential_zero_coefficients_identity` (the x-component reduces to R·ε_x when tangential coefficients are zero). This is both a sanity check on the definition and a regression guard against future changes that accidentally break the identity case.

**Domain safety.** The radial polynomial denominator is proved nonzero — and therefore safe for division — when all denominator coefficients k2, k4, k6 are zero. The proof provides a concrete witness for the `denominatorNonzero` predicate and proves by counterexample (k2 = −1, r = 1 makes the denominator exactly zero) that the predicate is genuinely constraining rather than always true.

**ΔP and ΔC translation consistency.** The campaign proves `distortion_center_translation_commutes`: substituting `ε_d = ε'_d + ΔP` (Equation 13) into the Equation 4 argument `ε_d − ΔC − ΔP` yields `ε'_d − ΔC`, which is exactly the Equation 10 argument. Algebraically: `(ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC`. This is the key structural fact underlying the projection/FOV equivalence: both characterizations apply U to the same distortion-centered argument, so they must agree on the output of U.

**Projection and FOV structural consistency.** The theorem `fov_undistort_eq` proves that the projection-form undistortion of `ε'_d + ΔP` equals the FOV-form undistortion of `ε'_d` plus ΔP. This is the formal version of the claim "the two characterizations are equivalent under the ΔP translation." The proof is nontrivial: the two domain hypotheses (denominatorNonzero proofs for the two forms) are propositionally equal by the commutation lemma but definitionally distinct, requiring a congruence helper lemma that appeals to Lean 4's proof irrelevance.

**Shader coordinate roundtrips.** The campaign proves that `fromShaderCoords ∘ toShaderCoords = identity` and `toShaderCoords ∘ fromShaderCoords = identity`, both requiring positive sensor width, height, and shader width. These proofs use `field_simp` to clear denominators; one direction requires a trailing `ring` call to close a residual arithmetic goal that `field_simp` leaves unsimplified. These theorems confirm that the metric-to-shader and shader-to-metric conversions are mutual inverses under the positivity conditions that any physical sensor satisfies.

**Angle of view.** The campaign proves that `tan(angleOfView(F, r_u) / 2) = r_u / F`, connecting the angle-of-view definition to its trigonometric interpretation via Mathlib's `Real.tan_arctan`.

---

## 7. Vacuity Auditing and Proof Discipline

A theorem that compiles is not necessarily meaningful. A theorem that states a genuinely false claim but carries an impossible precondition will compile and the proof will be accepted by the kernel. A theorem that reduces to `a + b − b = a` for all values of a and b is formally correct but contributes no domain knowledge. The campaign applied a systematic vacuity audit after all slices were complete to check for these failure modes.

The audit checks several patterns.

**Definitional tautologies.** The theorem `projection_matrix_undistort_eq` proves that removing the ΔC+ΔP offset from the output of `undistortFromDistorted` recovers the raw `undistortPoint` output. After unfolding the definition, this reduces to `a + b + c − b − c = a`, proved by `ring`. The theorem is correct, it compiles, and the audit marks it as a *partial structural consistency theorem*, not a proof of Equation 3/Equation 4 equivalence. A reader who saw only the theorem name might believe more was proved than was. The audit required adding an explicit scope-limitation comment.

**Formally identical theorems.** `deltaP_characterisation` and `deltaC_characterisation` are mathematically α-equivalent: they prove the same algebraic fact `sub(add(a, b), b) = a` with different variable names and identical proof scripts. Both are retained for equation traceability to Equations 12 and 13, but the audit required explicitly documenting that their distinctness is interpretive (different coordinate-space roles) rather than formal.

**Junk-value coverage.** `angle_of_view_eq` is stated for all `F : ℝ` including F = 0. At F = 0, Lean 4's total division yields `r_u / 0 = 0`, which makes both sides of the equation equal to zero without any physical meaning. The theorem holds for F = 0 via junk-value arithmetic, not optics. The audit confirmed this is documented in the file and is benign given that callers enforce F > 0 through `ValidLensSemantics`.

**Float oracle architecture drift.** The exact-real and Float layers have different function signatures. The exact `undistortX` takes a `denominatorNonzero` proof and calls `radialTerm` internally. The Float `undistortX_float` takes a pre-computed `R : Float` and has no domain proof — domain validity is handled by the `Option` return of `radialTerm_float`. No Lean theorem connects these architectures. The audit registers this as an open ambiguity (AMB-OL-016) and confirms it is contained by the Float oracle's explicit `⚠ FLOAT APPROXIMATION ONLY` warning. Future work connecting the two layers would require a separate campaign with IEEE 754 error bound machinery.

**Assumption satisfiability.** The audit checked that every hypothesis in every theorem has a concrete satisfying instance. The `denominatorNonzero` predicate is satisfiable (by setting k2 = k4 = k6 = 0, the denominator is always 1). No empty-domain theorems were found.

The overall audit verdict was *accepted with findings*. No stop-ship issues were found. Several scope-limitation comments and artifact improvements were required.

---

## 8. Differential Testing and Interoperability Infrastructure

The longer-term goal of the campaign is proof-backed interoperability testing: the ability to run external implementations — the Mo-Sys C++ reference, CamDKit in Python, renderer-side implementations — against the formal semantic model and detect disagreements.

The current infrastructure provides two layers. The Lean Float oracle in `ExecutableSemanticOracle.lean` can in principle be compiled to a native binary that evaluates the complete pipeline for given inputs. The Python reference oracle in `reference_oracle.py` independently implements every function from the OpenLensIO v1.0.1 specification, without reference to the Lean code. Both are tested against the same fixture suite. When external implementations become available for comparison, the fixture suite can be run against all implementations simultaneously; any divergence in outputs identifies an implementation that computes something different from the formal model.

At the time of this campaign, neither the Mo-Sys C++ implementation nor CamDKit exposes an undistort function at the API level that can be tested directly. The campaign documents this as a blocked dependency (OL-15). When access becomes available, the fixture infrastructure is ready.

The value of proof-backed testing over ordinary unit testing is that disagreements can be traced to specific specification claims rather than to informal test oracles. If the Lean oracle and an external implementation disagree on the output for a barrel-distortion input, the question becomes: which one implements the formal specification correctly? The Lean oracle is connected — at least structurally — to proved theorems about the mathematical definitions. The external implementation can be checked against the same definitions.

---

## 9. Proof Boundaries and Deferred Work

The following properties are explicitly not proved in this campaign.

**Forward distortion model.** The campaign formalizes undistortion U but not the forward distortion D (the function from undistorted coordinates to distorted coordinates). Without D, roundtrip properties such as `U(D(ε)) = ε` or `D(U(ε)) = ε` cannot be stated or proved. Full Eq(3)/Eq(4) forward/inverse equivalence is deferred (OL-DEFER-03). The specification itself notes that computing `D` requires iterative numerical methods.

**Invertibility and continuity.** The campaign does not prove that U is injective, surjective, or invertible. It does not prove continuity or monotonicity of the distortion model. These properties are plausible for well-calibrated lens coefficients but require stronger analytical machinery than the campaign's algebraic and polynomial tooling.

**Overscan semantics.** The overscan equations (Equations 8 and 15) have an unresolved asymmetry in how they handle ΔC and ΔP. No overscan theorems are attempted in this campaign.

**Float correctness.** The Float oracle is not proved to approximate the exact-real definitions within any error bound. The exact-real and Float semantics are intentionally kept separate. `radialTerm_float` uses an absolute tolerance of 1e-10 as its domain check, while the exact `denominatorNonzero` predicate requires strict ≠ 0. These semantics are different, and no bridging theorem is claimed.

**Complete OpenCV/OpenLensIO equivalence.** The campaign does not prove that any OpenLensIO lens calibration is equivalent to any OpenCV calibration. The theorems establish what the OpenLensIO model computes. The comparison to OpenCV requires either a formal model of OpenCV or a compositional equivalence proof connecting the two coordinate frames, neither of which is in scope.

**Renderer correctness.** Nothing in this campaign reaches renderer behavior. The pipeline is verified from sensor coordinates to shader coordinates and back. What the renderer does with shader coordinates is outside the formal model.

**Executable extraction correctness.** The Float oracle is testing infrastructure, not a verified executable. It has not been proved to implement the specification.

---

## 10. Conclusion

Formal verification of a protocol parser is necessary but not sufficient for semantic interoperability. Camera implementations can agree at the data layer and disagree at the geometric layer. The OpenLensIO semantic verification campaign makes the disagreement surface visible by formalizing the complete distortion and projection pipeline in exact-real arithmetic, proving structural theorems about its key properties, and building executable infrastructure for differential testing.

The campaign's primary practical contributions are:

- A formal specification of the Brown-Conrady distortion pipeline in terms of executable Lean 4 definitions, enabling proof-backed reasoning about what the pipeline computes.
- Structural consistency proofs connecting the projection and FOV characterizations, confirmed to rely on a specific sign convention in the specification (Equation 13 as authoritative over a contradicting inline statement).
- An executable semantic oracle suitable for differential testing against external implementations, with a Python reference harness and fixture suite ready for cross-implementation comparison.
- A documented catalogue of 16 semantic ambiguities in the specification, several of which have material impact on interoperability and at least one of which (the ΔP sign) is likely a specification typo.
- A formal proof discipline, including vacuity auditing, that confirms the proved theorems are meaningfully stated and not trivially true for the wrong reasons.

The result is not a complete camera model verification. It is a semantic interoperability foundation: a formal artifact that says precisely what the OpenLensIO pipeline computes, with explicit proof boundaries, and infrastructure to test whether external implementations agree.

---

*The proof campaign is developed in the opentrackio-proof repository. All Lean source files, LAPS artifacts, and the Python differential testing harness are included. The campaign targets Lean 4 with Mathlib v4.29.0.*
