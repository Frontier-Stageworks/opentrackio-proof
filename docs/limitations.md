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
proves the x-pixel coordinate. The y-component follows by p₁↔p₂ symmetry from the
x-theorem — the proof structure is identical with tangential terms swapped
(p₁(r²+2y²)+2p₂xy instead of 2p₁xy+p₂(r²+2x²)) and F=h/h_shader·fy in place of
F=w/w_shader·fx. No formal proof is planned; any reader can verify the y-result by
inspection of the x-proof.

**No full 2D pixel equivalence theorem.** A single theorem combining x and y into
a joint point-level iff (`ws/w = fx ∧ hs/h = fy`) is not proved. This would have
value as a clean downstream interface but is not planned; the x-theorem plus the
p₁↔p₂ symmetry argument covers the content.

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

**Suspected paper-level tangential conversion error (open question, not resolved
in this repository's formalization).** `DistortionConversion.lean` and
`Pipeline/PixelIff.lean` faithfully formalize the source paper's stated
tangential consistency condition (`δx_oti = δx_cv`, no scale factor), which
the paper derives to `q1 = p1/F², q2 = p2/F²`, and correctly finds that full
pixel agreement then additionally requires `ws/w = fx`. A companion
investigation (`DistortionConversionCorrected.lean`,
`Pipeline/PixelIffCorrected.lean`; not part of the as-published
formalization and not modifying it) argues from the paper's own coordinate
map `ε'_x,d = F·x''` that the tangential displacement — being additive,
unlike the multiplicative radial term — should convert with one factor of F
(`δx_oti = F·δx_cv`), giving `q1 = p1/F, q2 = p2/F`. Under that correction,
`opencv_openlensio_full_pipeline_pixel_corrected` proves full pixel agreement
holds unconditionally (no `ws/w = fx` requirement survives), and
`physical_pixel_agreement_scale_independent_example` exhibits a concrete
case with `ws/w ≠ fx` where pixel agreement still holds — machine-checked
evidence that the naive analog of the existing iff would be false under the
corrected hypotheses. This is presented as an open question about the
source paper's derivation, not as a correction accepted into the
as-published formalization; resolving it one way or the other would require
either an erratum from the paper's authors or independent confirmation
against a reference implementation. See
`docs/laps/tangential-conversion-physical-fix/` for the full derivation.

**Pipeline theorems prove same-direction (U→D) conjugacy, not native
OpenLensIO (D→U) undistortion consumption — still open.** All pipeline
theorems (`opencv_openlensio_full_pipeline_pixel_iff`/`_sufficiency`/
`_corrected`) compare OpenCV's forward-distortion formula against the same
formula shape applied to converted coefficients — both U→D evaluations. The
OpenTrackIO JSON schema's `distortion.model` defaults to `"Brown-Conrady
D-U"` (the opposite direction) when omitted. Whether real OpenTrackIO
producers/consumers are expected to set `model = "Brown-Conrady U-D"`
explicitly, or some other resolution is intended, is not addressed by the
paper or by this repository's proofs.

`inverse_approximation/InverseApproximation.lean` investigates this
direction generically (independent of OpenCV/OpenTrackIO units and
coefficients), in stages: a bounded-error estimate for a first-order
*approximate* inverse (`inverse_approx_error`); injectivity of the forward
map `D θ t` on the disk under the contraction condition `|t| * L θ R < 1`
(`D_eq_implies_eq`/`D_injective_on_disk`), plus the self-mapping and
contraction prerequisites a Banach fixed-point argument needs
(`inverse_step_maps_disk`/`inverse_step_lipschitz`); and finally, local
existence and uniqueness of the *true* inverse itself
(`D_exists_unique_preimage`, via Mathlib's Banach fixed-point theorem): for
every `y` in a buffer disk there is exactly one `z` in the disk with
`D θ t z = y`. `|t| * L θ R < 1` is a demonstrated *sufficient* condition
for this, not shown necessary.

None of this resolves the D-U/U-D question above. `D_exists_unique_preimage`
is a standalone mathematical fact about the polynomial (non-rational)
Brown-Conrady model, independent of and not contingent on how the
OpenTrackIO maintainers answer it — its relevance to that
interoperability question is separate and open, not established or implied
by the theorem itself. See `docs/specification-questions.md` (SQ-CV-07),
`inverse_approximation/README.md`, `docs/laps/bounded-inverse-approximation/`,
`docs/laps/inverse-injectivity/`, and `docs/laps/inverse-existence/` for
full scope and derivation.

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
