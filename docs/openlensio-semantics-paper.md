# Executable Semantics for OpenLensIO

Parser correctness is not semantic correctness. Two implementations can decode identical byte sequences to identical numeric values and still render different images, because the coordinate systems and composition order of their lens models differ. This work formalizes the OpenLensIO v1.0.1 lens model in Lean 4 as executable function definitions and proves structural correctness theorems about those definitions. The formal model spans 11 Lean source files and 14 public theorems, together with a Python differential testing harness.

A prior verification established parser correctness for the OpenTrackIO data model: encoders and decoders are mutual inverses, decoders are sound with respect to structural invariant predicates, and semantic extraction is sound with respect to a minimal validity predicate. Those results are useful, but they answer the wrong question for interoperability. Interoperability at the data level means two systems agree on numeric values. Interoperability at the semantic level means those values, when consumed by a camera model, produce the same geometric result. The gap between those properties is where rendering disagreements live in practice.

---

## Why semantic interoperability matters

Consider two implementations that both decode OpenLensIO tangential distortion coefficients p1 and p2 correctly — they agree on the values. But if one evaluates the tangential correction in coordinates centered at the distortion center while the other evaluates it in coordinates centered at the image principal point, they apply a different correction at every pixel. The images disagree. The disagreement is not a parsing bug. It is a coordinate-frame semantic bug.

This is not hypothetical. The OpenCV lens model and the OpenLensIO lens model both use Brown-Conrady tangential distortion with coefficients named p1 and p2. Their formulas look similar. But OpenLensIO specifies that undistortion U is applied to the coordinate `ε_d − ΔC − ΔP`, where ΔC is the distortion center offset and ΔP is the perspective offset. The tangential correction is therefore evaluated in the distortion-center frame. OpenCV's convention is different. A camera tracker that exports OpenLensIO coefficients and a renderer that imports them as OpenCV coefficients will produce different renders even when both sides implement their respective specifications exactly.

Parser tests cannot catch this class of disagreement. Unit tests on isolated functions may miss it if both implementations validate against their own internal conventions. The only reliable approach is to formalize what the specification says the pipeline should compute, and test implementations against that formal model.

---

## From parser correctness to camera semantics

A prior proof established that data written in OpenTrackIO format can be read back accurately. It does not establish any claim about what happens after the data is read.

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

Each step is an opportunity for a semantic disagreement: an offset applied in the wrong direction, a transformation applied in the wrong order, or coordinates from the wrong frame fed to the next stage. Each step is encoded as a Lean 4 function definition, and structural invariants connecting them are proved. The key shift is from asking "does the decoder produce the right struct?" to "does that struct, when consumed by the camera model, produce the right coordinates?" These questions are genuinely different, and formalizing them exposes disagreements that neither testing nor prose reading of the specification reliably surfaces.

---

## Coordinate systems and specification questions

Formalizing the OpenLensIO model surfaced several semantic questions. Most are genuine interoperability hazards, not notation preferences. Formalization raised 16 questions about the specification. Ten remain open; five were resolved as non-issues (the ΔP sign convention, the diagonal U notation, the aperture formula's non-normative status, the overscan appendix's informative status, and the distortion-center frame being derivable from call sites); and one concerns the Float-to-exact-real architecture gap rather than the specification itself (discussed in the Scope and Caveats section).

**The ΔP coordinate relationship.** The specification states the projection/FOV coordinate relationship consistently: both Equation 13 and the inline text near Equation 10 write `ε_d = ε'_d + ΔP` in the same form. The sign convention is load-bearing: all theorems relating the FOV and projection characterizations depend on it, and an implementation encoding the wrong direction produces incorrect output for any lens with nonzero ΔP.

**The distortion-center frame.** Undistortion U is applied to the shifted coordinate `ε_d − ΔC − ΔP`. The tangential correction inside U uses a radius r computed from this shifted point. An implementation that computes r from the unshifted coordinate produces a subtly wrong result — one that may be undetectable without a calibration target with large tangential distortion.

**The rational radial polynomial's denominator.** The radial factor R is a degree-6 rational polynomial in r². The denominator can in principle be zero for pathological coefficient values. The specification is silent on this. The formal model makes it explicit: `denominatorNonzero` is a per-point domain predicate that callers must supply, making the failure mode impossible to ignore at the call site.

**The FOV and projection characterizations.** OpenLensIO defines two parameterizations of the same lens: the projection matrix form (with ΔP) and the FOV form (without ΔP, using optical-axis-centered coordinates). The specification states they are equivalent under the ΔP translation but does not prove it. Formally establishing this connection is one of the primary results.

**The overscan offset inconsistency.** The overscan equations (Equations 8 and 15) drop the ΔC and ΔP offsets asymmetrically between the two forms. The specification does not explain the asymmetry. Overscan proofs are deferred pending resolution.

---

## Executable semantic modeling

The formal model defines the complete OpenLensIO semantic pipeline as Lean 4 functions — sensor radius, radial term, Brown-Conrady undistortion components, projection and FOV forms, shader coordinate conversion, angle-of-view equations — and proves theorems about those functions. This matters for two reasons: theorems about concrete functions can be tested against external implementations, and defining a function forces every specification question to be resolved. A function that actually computes cannot leave coordinate frames or signs unspecified.

All semantic functions are defined over exact real numbers (ℝ) using Mathlib's noncomputable infrastructure. This is the layer that carries formal proofs. A parallel executable Float layer provides `undistortPoint_float`, `undistortFromDistorted_float`, and so on, in a separate file that opens with an explicit warning: these are IEEE 754 double-precision approximations, not verified implementations. No theorem connects Float behavior to the exact-real semantics; that bridge would require error-bound machinery that is outside the scope of this work.

A Python reference implementation independently implements every formula from the specification, without reference to the Lean code. Both the Float functions and the Python implementation are tested against a shared fixture suite of seven hand-computed cases: the zero-coefficient identity, barrel and pincushion radial distortion, the optical-axis boundary, tangential-only distortion, denominator-near-zero domain failure, and a full Equation 4 pipeline case. Both pass all seven. This confirms the two independently-written implementations agree on the formulas; it is not a formal proof of either.

The exact-real and executable layers serve different purposes and are kept strictly separate. The exact-real layer is the specification. The Float layer and Python implementation are testing infrastructure.

---

## Key theorems

The 14 public theorems fall into three groups.

**Model correctness under degenerate inputs.** With all radial and tangential coefficients zero, undistortion returns its input unchanged. This is both a sanity check on the definition and a regression guard: any change that accidentally breaks the identity case fails to compile. A supporting theorem proves that when the denominator polynomial coefficients are all zero, the denominator is identically 1 and therefore always nonzero. The counterexample k₂ = −1, r = 1 produces a zero denominator, confirming that the domain predicate is genuinely constraining rather than always satisfied.

**Pipeline structural consistency.** The central structural result connects the FOV and projection characterizations. The argument to U in the projection form is `ε_d − ΔC − ΔP`. Substituting `ε_d = ε'_d + ΔP` (Equation 13) yields `ε'_d − ΔC`, which is exactly the argument to U in the FOV form. The ΔP terms cancel, so both characterizations apply U to the same distortion-centered coordinate. The formal model proves this cancellation, then proves the full consistency result: the projection-form undistortion of `ε'_d + ΔP` equals the FOV-form undistortion of `ε'_d` plus ΔP. The proof requires a congruence lemma bridging two formally distinct but propositionally equal domain hypotheses — the two pipeline forms carry differently-typed domain evidence for the same mathematical condition.

**Coordinate transformations.** The shader-coordinate roundtrip theorems prove that the metric-to-shader and shader-to-metric conversions are mutual inverses, under the positivity conditions (sensor width, height, and shader width all positive) satisfied by any physical sensor. The angle-of-view theorem confirms the trigonometric relationship `tan(α/2) = r_u / F`, connecting the formal definition to the specification's stated equation.

---

## Scope and caveats

Formal verification establishes precise claims with precise preconditions. Several scope limits are worth naming explicitly.

**Definitional tautology.** The projection offset cancellation theorem, after unfolding `undistortFromDistorted`, reduces to `a + b + c − b − c = a`. This correctly documents that the definition has the right offset structure, but it does not prove that the projection and FOV forms agree on outputs — the full consistency theorem above is the result that does.

**Formally identical theorems.** Two theorems about ΔP and ΔC translation prove the same algebraic fact with different variable names. Both are retained for traceability to specific specification equations; their distinctness is interpretive (coordinate-space roles differ), not formal.

**Junk-value coverage.** The angle-of-view theorem holds for all focal lengths including F = 0. At F = 0, Lean 4's total real-number division yields 0/0 = 0, making both sides zero — technically true for junk-value arithmetic reasons rather than optics. All call sites enforce F > 0 through `ValidLensSemantics`; this behavior is documented in the source.

**Float architecture.** The exact-real and Float layers have structurally different function signatures: exact functions carry domain proofs in their types, while Float functions handle domain failure through `Option` returns. No theorem connects these architectures. Any bridging work — requiring IEEE 754 error-bound machinery — is deferred.

**Assumption satisfiability.** Every hypothesis in every theorem has at least one concrete satisfying instance. The domain predicate `denominatorNonzero` is satisfiable by setting denominator coefficients to zero; `ValidLensSemantics` is satisfiable by any lens with positive focal length. No vacuous theorems were found.

---

## Differential testing and interoperability

The longer-term goal is proof-backed interoperability testing: running external implementations against the formal semantic reference model to detect disagreements. Any divergence identifies an implementation computing something different from the formal specification.

Two testing layers are in place. The Lean Float functions in `ExecutableSemanticOracle.lean` can be compiled to a native binary that evaluates the complete pipeline for given inputs. The Python reference implementation independently computes the same formulas. Both are validated against the same fixture suite; external implementations will be run against those same fixtures. When an external implementation disagrees with a fixture's expected value, the question becomes: which one correctly implements the formal specification? The executable semantic reference — connected structurally to proved theorems about the exact-real definitions — provides a traceable answer.

At the time of this writing, neither the Mo-Sys C++ implementation nor CamDKit exposes an undistort function at the API level suitable for direct comparison. The fixture infrastructure is ready when access becomes available.

The value of proof-backed testing over ordinary unit testing is traceability. An ordinary test oracle is a program someone wrote and believes is correct. A proof-backed reference is connected to a machine-checked formal specification. Disagreements can be traced to specific specification claims rather than to informal judgment about what the formula was supposed to compute.

---

## What is not proved

**Forward distortion model.** Undistortion U is formalized; the forward distortion D is not. Without D, roundtrip properties such as `U(D(ε)) = ε` cannot be stated. The specification notes that D requires iterative numerical methods. Full forward/inverse equivalence is deferred.

**Invertibility and continuity.** U is not proved injective, surjective, or invertible, and continuity and monotonicity are not addressed. These properties are plausible for well-calibrated lenses but require analytical machinery beyond the algebraic tooling used here.

**Overscan semantics.** The overscan equations have an unresolved asymmetry in how ΔC and ΔP are handled. No overscan theorems are attempted.

**Float correctness.** The Float implementation is not proved to approximate the exact-real definitions within any error bound. The domain check in the Float layer uses an absolute tolerance of 1e-10, while the exact predicate requires strict inequality with zero. These semantics differ, and the separation is intentional.

**Complete OpenCV/OpenLensIO equivalence.** This work establishes what the OpenLensIO model computes. Comparing it to OpenCV requires a formal model of OpenCV's conventions and a compositional equivalence proof across coordinate frames — neither of which is in scope.

**Renderer correctness.** The pipeline is formally verified from lens parameters to shader coordinates. What the renderer does with those coordinates is outside the formal model.

---

## Conclusion

Parser correctness is the floor, not the ceiling, of interoperability. Camera implementations can agree at the data layer and disagree at the geometric layer, and those disagreements can be invisible to ordinary testing if both sides validate against their own conventions.

The practical contributions of this work are:

- A formal executable semantic reference model for the Brown-Conrady distortion pipeline, defined in exact-real arithmetic and kernel-verified by Lean 4, that can serve as ground truth for cross-implementation comparison.
- Structural consistency proofs connecting the projection and FOV characterizations, with a load-bearing dependency on a specific sign convention in the specification — a dependency that ordinary implementation testing would not have surfaced as a named, trackable assumption.
- A Python differential testing implementation and shared fixture suite, ready to run against external implementations (Mo-Sys C++, CamDKit, renderer pipelines) as API access becomes available.
- A catalogue of 10 open specification questions, several with material interoperability impact. The most consequential are the denominator nonzero condition left implicit in the specification, the U⁻¹ inversion described only as an iterative numerical procedure with no closed form, and the asymmetric ΔC/ΔP handling in the overscan equations that remains unexplained.

The formalization process itself surfaces what prose reading misses. The ΔP coordinate relationship required verifying that both the projection and FOV forms apply undistortion to the same distortion-centered argument. The distortion-center frame semantics were clarified because a function definition cannot leave them implicit. The overscan asymmetry had to be deferred rather than silently resolved. These are the specification questions that any implementation must answer, made explicit and traceable.

That is the practical value of this work: it turns OpenLensIO from a convention that implementations roughly follow into a precise executable specification that implementations can be tested against.
