# Executable Semantics for OpenLensIO: Formal Verification of Camera-Model Interoperability

**Mark Stalzer**
*opentrackio-proof project*

---

## Abstract

Parser correctness is not semantic correctness. Two implementations can decode identical byte sequences to identical numeric values and still render different images, because the coordinate systems and composition order of their lens models differ. This paper describes a Lean 4 formal verification campaign that extends beyond parser roundtrip proofs into executable camera-model semantics for the OpenLensIO lens model. We formalize the Brown-Conrady distortion pipeline, prove structural consistency theorems connecting the projection and FOV characterizations, and build an executable semantic reference model suitable for differential testing against external implementations. A central finding is that the OpenLensIO and OpenCV tangential distortion models operate in different coordinate frames: coefficient equality does not imply semantic equivalence, and interoperability must be established compositionally. We describe the proof architecture, the specification ambiguities uncovered during formalization, the vacuity audit discipline applied to the campaign, and the explicit boundaries of what has and has not been verified.

---

## 1. Introduction

The OpenTrackIO standard specifies a JSON protocol for camera tracking metadata in virtual production. A previous verification campaign established parser correctness: the encoder and decoder are mutual inverses, the decoder is sound with respect to a structural invariant predicate, and semantic extraction is sound with respect to a minimal validity predicate. Those results are useful, but they answer the wrong question for interoperability.

Interoperability at the data level means that two systems agree on numeric values. Interoperability at the semantic level means that those values, when consumed by a camera model, produce the same geometric result. The gap between these properties is where rendering disagreements live in practice.

This campaign addresses the semantic level. We formalize the OpenLensIO v1.0.1 lens model in Lean 4, prove structural correctness theorems about its distortion and projection pipeline, and apply a systematic vacuity audit to ensure the formal results are not technically correct but semantically empty. The campaign spans 11 Lean source files and 14 public theorems, together with a Python differential testing harness.

Using Lean 4 for this work provides specific operational advantages that prose specifications and test suites cannot match. Definitions are machine-checked; theorems about them are kernel-verified. Every hypothesis is named and tracked — an assumption cannot be silently introduced to make a proof work. Downstream theorems break as compile errors when definitions change, making semantic drift detectable. And the formal model produces executable code that can be run against external implementations.

---

## 2. Why Semantic Interoperability Matters

Consider two implementations that both decode OpenLensIO tangential distortion coefficients p1 and p2 correctly — they agree on the values. But if one evaluates the tangential correction in coordinates centered at the distortion center while the other evaluates it in coordinates centered at the image principal point, they apply a different correction at every pixel. The images disagree. The disagreement is not a parsing bug. It is a coordinate-frame semantic bug.

This is not hypothetical. The OpenCV lens model and the OpenLensIO lens model both use Brown-Conrady tangential distortion with coefficients named p1 and p2. Their formulas look similar. But OpenLensIO specifies that undistortion U is applied to the coordinate `ε_d − ΔC − ΔP`, where ΔC is the distortion center offset and ΔP is the perspective offset. The tangential correction is therefore evaluated in the distortion-center frame. OpenCV's convention is different. A camera tracker that exports OpenLensIO coefficients and a renderer that imports them as OpenCV coefficients will produce different renders even when both sides implement their respective specifications exactly.

Parser tests cannot catch this class of disagreement. Unit tests on isolated functions may miss it if both implementations validate against their own internal conventions. The only reliable approach is to formalize what the specification says the pipeline should compute, and test implementations against that formal model — which is what this campaign provides.

---

## 3. From Parser Correctness to Camera Semantics

The prior campaign established that data written in OpenTrackIO format can be read back accurately. What it does not establish is any claim about what happens after the data is read.

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

Each step is an opportunity for a semantic disagreement: an offset applied in the wrong direction, a transformation applied in the wrong order, or coordinates from the wrong frame fed to the next stage. The formal campaign makes each step explicit as a Lean 4 function definition, then proves structural invariants connecting them. The key shift is from asking "does the decoder produce the right struct?" to "does that struct, when consumed by the camera model, produce the right coordinates?"

These questions are genuinely different, and formalizing them exposes disagreements that neither testing nor reading the specification in prose reliably surfaces.

---

## 4. Coordinate Systems and Specification Ambiguities

Formalizing the OpenLensIO model required resolving several semantic ambiguities. Most are genuine interoperability hazards, not notation preferences. The campaign maintains an explicit ambiguity register; 16 entries were recorded, with 15 extracted directly from the specification and one arising from the Float-to-exact-real architecture gap (discussed in Section 7).

**The ΔP coordinate relationship.** The specification states the projection/FOV coordinate relationship in two equivalent forms: Equation 13 writes `ε_d = ε'_d + ΔP` (ε_d isolated), and inline text near Equation 10 writes `ε'_d = ε_d − ΔP` (ε'_d isolated) — algebraically identical rearrangements. Formalizing this required encoding the relationship as a concrete Lean 4 function and verifying it carries through the pipeline correctly. The choice is load-bearing: all theorems relating the FOV and projection characterizations depend on the correct sign convention, and an implementation encoding the wrong direction will produce incorrect output for any lens with nonzero ΔP.

**The distortion-center frame.** Undistortion U is applied to the shifted coordinate `ε_d − ΔC − ΔP`. The tangential correction inside U therefore uses a radius r computed from this shifted point. An implementation that computes r from the unshifted coordinate will produce a subtly wrong result — one that may be undetectable without a calibration target with large tangential distortion.

**The rational radial polynomial's denominator.** The radial factor R is a degree-6 rational polynomial in r². The denominator can in principle be zero for pathological coefficient values. The specification is silent on this. The formal model resolves it explicitly: `denominatorNonzero` is a per-point domain predicate that callers must supply, making the failure mode impossible to ignore at the call site.

**The FOV and projection characterizations.** OpenLensIO defines two parameterizations of the same lens: the projection matrix form (with ΔP) and the FOV form (without ΔP, using optical-axis-centered coordinates). The specification states they are equivalent under the ΔP translation but does not prove it. Formally verifying this connection is one of the campaign's primary goals.

**The overscan offset inconsistency.** The overscan equations (Equations 8 and 15) drop the ΔC and ΔP offsets asymmetrically between the two forms. The specification does not explain the asymmetry. This remains an open ambiguity and overscan proofs are deferred.

---

## 5. Executable Semantic Modeling

Rather than proving properties about abstract descriptions, the campaign formalizes the complete OpenLensIO semantic pipeline as Lean 4 function definitions — sensor radius, radial term, Brown-Conrady undistortion components, projection and FOV forms, shader coordinate conversion, angle-of-view equations — and then proves theorems about those functions. This matters for two reasons: theorems about concrete functions can be tested against external implementations, and defining a function forces every specification ambiguity to be resolved. A function that actually computes something cannot leave coordinate frames or signs unspecified.

All semantic functions are defined over exact real numbers (ℝ) using Mathlib's noncomputable infrastructure. This is the layer that carries formal proofs. Alongside it, the campaign produces an executable Float counterpart for every function — `undistortPoint_float`, `undistortFromDistorted_float`, and so on — in a separate file that opens with an explicit warning: these are IEEE 754 double-precision approximations, not verified implementations. There is no bridging theorem connecting Float behavior to exact-real semantics, and writing one would require error-bound machinery that is out of scope.

A Python reference implementation independently implements every formula from the specification, without reference to the Lean code. Both the Float functions and the Python implementation are tested against a shared fixture suite of seven hand-computed cases: the zero-coefficient identity, barrel and pincushion radial distortion, the optical-axis boundary, tangential-only distortion, denominator-near-zero domain failure, and a full Equation 4 pipeline case. Both pass all seven. This gives confidence that the two independently-written implementations agree on the formulas without constituting a formal proof of either.

The exact-real and executable layers serve different purposes and are kept strictly separate. The exact-real layer is the specification. The Float layer and Python implementation are testing infrastructure.

---

## 6. Key Verification Results

The campaign's 14 public theorems fall into three groups.

**Model correctness under degenerate inputs.** The zero-distortion identity theorem proves that with all radial and tangential coefficients set to zero, the undistortion function returns its input unchanged. This is both a sanity check on the definition and a regression guard: any future change that accidentally breaks the identity case will fail to compile. Supporting this is a denominator domain theorem proving that when the denominator polynomial coefficients are all zero, the denominator is identically 1 and therefore always nonzero. Crucially, the counterexample k2 = −1, r = 1 produces a zero denominator, demonstrating that the domain predicate is genuinely constraining rather than always satisfied.

**Pipeline structural consistency.** The central structural result is the connection between the FOV and projection characterizations. The argument to U in the projection form is `ε_d − ΔC − ΔP`. Substituting `ε_d = ε'_d + ΔP` (Equation 13) yields `ε'_d − ΔC`, which is exactly the argument to U in the FOV form. The ΔP terms cancel. This means both characterizations apply U to the same distortion-centered coordinate — they must agree on what U returns. The campaign proves this cancellation lemma and then proves the full consistency theorem: the projection-form undistortion of `ε'_d + ΔP` equals the FOV-form undistortion of `ε'_d` plus ΔP. The proof requires a congruence lemma that bridges two formally distinct but propositionally equal domain hypotheses, which is nontrivial because the two pipeline forms carry differently-typed domain evidence for the same mathematical condition.

**Coordinate transformations.** The shader-coordinate roundtrip theorems prove that the metric-to-shader and shader-to-metric conversions are mutual inverses, under the positivity conditions (sensor width, height, and shader width all positive) that any physical sensor satisfies. The angle-of-view theorem confirms the trigonometric relationship `tan(α/2) = r_u / F` that the angle-of-view definition inverts, connecting the formal definition to the specification's stated equation.

---

## 7. Vacuity Auditing and Proof Discipline

A theorem that compiles is not necessarily meaningful. A theorem carrying an impossible precondition — one that is never satisfiable — will compile, and the proof will be accepted by the kernel, but it proves nothing usable. A theorem that reduces by definition unfolding to `a + b − b = a` is formally correct but contributes no domain knowledge. After completing all proof slices, the campaign applied a systematic vacuity audit to check for these failure modes.

**Definitional tautology.** The projection offset cancellation theorem, after unfolding `undistortFromDistorted`, reduces to `a + b + c − b − c = a`. This is correct and useful as documentation that the definition has the right offset structure — but it is not a proof that the projection and FOV forms agree on outputs. The audit required adding a scope-limitation comment making explicit what the theorem does and does not prove.

**Formally identical theorems.** Two theorems about ΔP and ΔC translation prove the same algebraic fact with different variable names. Both are retained for traceability to specific paper equations, but the audit required documenting that their distinctness is interpretive — the coordinate-space roles differ — not formal.

**Junk-value coverage.** The angle-of-view theorem is stated for all focal lengths including F = 0. At F = 0, Lean 4's total real-number division yields 0/0 = 0, making both sides of the equation zero — technically true, but for junk-value arithmetic reasons rather than optics. This is benign because all call sites enforce F > 0 through `ValidLensSemantics`, and the behavior is documented in the source. A future authorized revision could add a nonzero hypothesis to the statement.

**Float architecture drift.** The exact-real and Float layers have structurally different function signatures: the exact functions carry domain proofs in their types, while the Float functions handle domain failure through `Option` returns. No theorem connects these architectures. The audit registers this as an open ambiguity, confirms the Float layer's warning is accurate, and defers any bridging work — which would require IEEE 754 error bound machinery — to a future campaign.

**Assumption satisfiability.** Every hypothesis in every theorem was checked to have at least one concrete satisfying instance. The domain predicate `denominatorNonzero` is satisfiable by setting denominator coefficients to zero; `ValidLensSemantics` is satisfiable by any lens with positive focal length. No empty-domain theorems were found.

The overall audit verdict was *accepted with findings*. No theorem needed to be withdrawn. Several scope-limitation comments and documentation improvements were required. This kind of audit is not optional: it is the step that separates "the proof compiles" from "the theorem means what we think it means."

---

## 8. Differential Testing and Interoperability Infrastructure

The longer-term goal is proof-backed interoperability testing: the ability to run external implementations against the formal semantic reference model and detect disagreements. Any divergence identifies an implementation computing something different from the formal specification.

The current infrastructure has two layers. The Lean Float functions in `ExecutableSemanticOracle.lean` can be compiled to a native binary that evaluates the complete pipeline for given inputs. The Python reference implementation independently computes the same formulas. Both are tested against the same fixture suite; the fixture suite is what external implementations will be run against. When an external implementation disagrees with the fixture expected values, the question becomes: which one correctly implements the formal specification? The executable semantic reference model — connected structurally to proved theorems about the exact-real definitions — provides a concrete answer.

At the time of this campaign, neither the Mo-Sys C++ implementation nor CamDKit exposes an undistort function at the API level suitable for direct comparison. This is a blocked dependency; the fixture infrastructure is ready when access becomes available.

The value of proof-backed testing over ordinary unit testing is traceability. An ordinary test oracle is a program someone wrote and believes is correct. A proof-backed reference is a program connected to a machine-checked formal specification. Disagreements can be traced to specific specification claims rather than to informal judgment about what the formula was supposed to compute.

---

## 9. Proof Boundaries and Deferred Work

The following are explicitly not proved in this campaign.

**Forward distortion model.** The campaign formalizes undistortion U but not the forward distortion D. Without D, roundtrip properties such as `U(D(ε)) = ε` cannot be stated. The specification notes that D requires iterative numerical methods, which is itself a claim the formal model does not address. Full forward/inverse equivalence is deferred.

**Invertibility and continuity.** The campaign does not prove U is injective, surjective, or invertible, and does not prove continuity or monotonicity. These properties are plausible for well-calibrated lenses but require analytical machinery beyond the algebraic tooling used here.

**Overscan semantics.** The overscan equations have an unresolved asymmetry in how ΔC and ΔP are handled. No overscan theorems are attempted.

**Float correctness.** The Float implementation is not proved to approximate the exact-real definitions within any error bound. The domain check in the Float layer uses an absolute tolerance of 1e-10, while the exact predicate requires strict inequality with zero. These semantics differ, and the separation is intentional. No bridging theorem is claimed.

**Complete OpenCV/OpenLensIO equivalence.** The campaign establishes what the OpenLensIO model computes. Comparing it to OpenCV requires a formal model of OpenCV's conventions and a compositional equivalence proof across coordinate frames — neither of which is in scope.

**Renderer correctness.** The pipeline is formally verified from lens parameters to shader coordinates. What the renderer does with those coordinates is outside the formal model.

---

## 10. Conclusion

Parser correctness is the floor, not the ceiling, of interoperability. Camera implementations can agree at the data layer and disagree at the geometric layer, and those disagreements can be invisible to ordinary testing if both sides validate against their own conventions. The OpenLensIO semantic verification campaign makes this failure mode concrete and addressable.

The campaign's practical contributions are:

- A formal executable semantic reference model for the Brown-Conrady distortion pipeline, defined in exact-real arithmetic and kernel-verified by Lean 4, that can serve as a ground truth for cross-implementation comparison.
- Structural consistency proofs connecting the projection and FOV characterizations, with a load-bearing dependency on a specific sign convention in the specification — a dependency that ordinary implementation testing would not have surfaced as a named, trackable assumption.
- A Python differential testing implementation and shared fixture suite, ready to run against external implementations (Mo-Sys C++, CamDKit, renderer pipelines) as API access becomes available.
- A catalogue of 16 specification ambiguities, several with material interoperability impact. The most consequential are the denominator nonzero condition left implicit in the specification, the distortion-center frame semantics that must be derived from context, and the asymmetric ΔC/ΔP handling in the overscan equations that remains unexplained.
- A vacuity audit confirming that the proved theorems are meaningfully stated, not trivially true, and correctly scoped.

This last point deserves emphasis. The formalization process itself — the act of writing definitions precise enough to carry proofs — exposed ambiguities and assumptions that prose reading of the specification did not. The ΔP coordinate relationship required explicit encoding and verification that both the projection and FOV forms apply undistortion to the same distortion-centered argument. The distortion-center frame semantics were clarified because a function definition cannot leave them implicit. The overscan asymmetry was registered because it could not be silently resolved; it had to be deferred.

The result is not a complete camera model verification. It is a step toward treating OpenLensIO not as a convention that implementations roughly follow, but as a precise executable specification that implementations can be tested against. That shift — from convention to verifiable executable semantics — is the practical goal of this work.

---

*The proof campaign is in the opentrackio-proof repository. All Lean source files, LAPS artifacts, and the Python differential testing harness are included. The campaign targets Lean 4 with Mathlib v4.29.0.*
