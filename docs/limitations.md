# Limitations

What is explicitly not proved in this repository. Read this before citing the proofs
as evidence of anything beyond what is listed here.

---

## OpenTrackIO Parser (`opentrackio_parser/`)

**No byte-level JSON parser.** The model operates on an already-parsed `JsonValue`
AST. Byte-level JSON parsing — character encoding, number formatting edge cases,
surrogate pairs, deeply-nested structure limits — is outside scope. Python or a
native JSON library parses JSON bytes before the Lean model sees them.

**`WellFormedSampleJson (encodeSample s)` not proved.** The normalization theorems
use `WellFormedSampleJson` as a precondition on inputs from outside the model.
That `encodeSample` itself produces well-formed JSON is not proved — a private-boundary
issue between `WellFormedSampleJson.lean` and `NormalizationTheorems.lean`.

**Numeric upper bounds not proved.** `PositiveRational` enforces strict positivity.
Frame rate ≤ 240, pixel count limits, angle ranges, and similar schema-level bounds
are not formalized. Values are type-checked but not range-checked.

**Regex and pattern constraints not proved.** UUID URNs, PTP leader identities,
firmware version strings, and similar pattern-constrained fields are stored as raw
`String` after being recognized as JSON strings. Pattern conformance is not verified.

**Duplicate-key behavior not enforced by `decodeSample`.** `lookup?` takes the first
matching key in a JSON object. Duplicate keys are handled only through the
`WellFormedSampleJson` predicate's `NoDupKeys` condition; `decodeSample` itself does
not reject inputs with duplicate keys.

**Decode → re-encode normalization is one-directional.** `encodeSample_roundtrip`
proves encode → decode. The inverse direction (decode arbitrary well-formed JSON →
encode → recover original JSON) is covered only after one normalize pass, via
`normalization_under_wellFormed`.

**`lake exe` native binary not built.** A Lean 4.29.0 / Darwin 25.3.0 linker
incompatibility prevents native `lake exe` linking. All proof obligations are fully
discharged; this is a packaging limitation only. The harness runs via
`lake env lean --run`.

---

## OpenLensIO Semantics (`openlensio_semantics/`)

**Forward distortion model: no closed-form D, nonconstructive inverse not yet stated.**
The spec defines D = U⁻¹ explicitly in Eqs (5) and (11) and asserts it exists. A
closed-form formula for D does not exist for the full Brown-Conrady model; the spec
prescribes numerical iteration for computing D. For p=0, `radialDescale_left_inverse_zero_tangential`
proves D(r, U(ε)) = ε with an explicit input-radius parameter (a conditional left
inverse, not a full inverse). A nonconstructive left-inverse theorem via `Function.invFun`
is not yet stated but is reachable from the injectivity results in `InjectivityModel.lean`.

**Injectivity: partially proved; surjectivity and continuity not proved.**
`undistortPoint` is proved injective on fixed-radius circles (with or without tangential
terms, under hypotheses) and globally for p=0 given a caller-supplied scale-injectivity
hypothesis. See `InjectivityModel.lean`. Global injectivity without the `hScaleInj`
hypothesis, surjectivity onto the intended range, and continuity/monotonicity are not
proved and require analytical machinery beyond the algebraic tactics used here.

**Overscan semantics deferred.** Equations 8 and 15 in the OpenLensIO specification
drop the ΔC and ΔP offsets asymmetrically between the two forms without explanation.
No overscan theorems are attempted pending resolution of this ambiguity.

**Float layer not formally connected to exact-real layer.** `ExecutableSemanticOracle.lean`
provides IEEE 754 double-precision implementations for differential testing. No
theorem proves these approximate the exact-real definitions within any error bound.
The domain check in the Float layer uses an absolute tolerance of `1e-10`; the
exact-real predicate requires strict inequality. The separation is intentional and
documented.

**Junk-value behavior at F = 0.** `angle_of_view_eq` holds for all focal lengths
including F = 0, where both sides compute to 0 via Lean's total real-number division.
This is technically correct but physically meaningless. All intended call sites enforce
`F > 0` through `ValidLensSemantics`.

---

## OpenCV ↔ OpenLensIO Conversion (`opencv_opentrackio_proofs/`)

**Pipeline iff is x-component only.** `opencv_openlensio_full_pipeline_pixel_iff`
proves the x-pixel coordinate. The y-component is symmetric (p1 ↔ p2 swapped) but
not yet written.

**No full 2D pixel equivalence theorem.** A single theorem combining x and y into
a joint point-level iff is not yet proved.

**Pure-radial case not characterized.** The iff requires `p1 ≠ 0 ∨ p2 ≠ 0`. When
both tangential coefficients are zero, `ws/w = fx` is not entailed by pixel
agreement (the tangential term that reveals the scale discrepancy is identically zero).
The behavior of purely-radial pipelines under mismatched scale is not separately
characterized.

**`denominatorNonzero` is a free hypothesis.** The proofs assume the radial
denominator polynomial is nonzero at every input point. Deriving this from
physically-meaningful coefficient bounds (denominator bounded away from zero over a
working radius range) is not proved.

**Conditional iff, not unconditional extraction.** All conversion hypotheses
(l_i = k_i/F^(2n), q_i = p_i/F², F = (w/ws)·fx, ΔPx = (w/ws)·(cx − ws/2)) are
given as context rather than extracted from pixel equality alone. The iff isolates
`ws/w = fx` as the remaining condition. Extracting all eleven conditions from pixel
equality alone would require rational function coefficient extraction and is not proved.

---

## Cross-cutting

**No renderer correctness proof.** All three proof areas stop at the mathematical
pipeline level. What a renderer, compositing engine, or LED-volume processor does
with the output coordinates is entirely outside scope.

**Specification ambiguities not resolved.** Several OpenLensIO specification questions
remain open — overscan asymmetry, denominator nonzero domain, forward inversion method.
See `docs/specification-questions.md` for the full list.

**No cross-proof-area composition theorem.** The three areas (parser, semantics,
conversion) are proved independently. There is no end-to-end theorem connecting
"a parsed OpenTrackIO sample" to "semantically correct pixel output." Building that
connection would require the domain validation layer and parsed-field linkage listed
in the pipeline future work.
