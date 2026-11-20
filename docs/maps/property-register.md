# Property Register

Phase 2/3 artifact for the OpenTrackIO protocol assurance effort (`opentrackio-proof`, `ris-osvp-metadata-camdkit`, `opentrackio-cpp`). See `system-assurance-map.md` for system understanding this register builds on.

## Register

### PROP-001: Cross-implementation decode-field agreement

- **Behavioral segment:** Protocol envelope / parser (camdkit `docs/arrows/protocol-envelope.md`; `opentrackio-proof/opentrackio_parser/`; `opentrackio-cpp` decode path)
- **Claim:** For a valid OpenTrackIO v1.0.1 JSON sample, camdkit, opentrackio-cpp, and the Lean decoder produce equal values for each of the 18 battery-tester comparison fields (protocol.name/version, tracker.slate/serialNumber, timing.*, camera.activeSensorResolution.*, transforms.Camera.*, lens.focusDistance, lens.pinholeFocalLength), within each field's stated tolerance.
- **Quantifiers in the claim:** for every valid sample in the 4 canonical fixtures and the 76-fixture generated corpus; for each of the 18 named fields.
- **Claim dimensions:**
  - decode agreement: camdkit vs Lean oracle
  - decode agreement: opentrackio-cpp vs Lean oracle
  - decode agreement: camdkit vs opentrackio-cpp
  - encode-side / full roundtrip agreement (camdkit, opentrackio-cpp) — not yet exercised
- **Implementation / representation surface:**
  - Claim dimension: camdkit vs Lean oracle / opentrackio-cpp vs Lean oracle / camdkit vs opentrackio-cpp
    - Implemented/enforced by: `camdkit.from_json`-equivalent path, `opentrackio-cpp` `dump_sample`, Lean `decodeSample`
    - Representation involved: parsed JSON → each implementation's internal sample representation → 18-field TSV extraction
    - Observable through: `battery-tester/run.py` differential comparison
  - Claim dimension: encode-side / full roundtrip agreement
    - Implemented/enforced by: n/a — not currently built for camdkit/opentrackio-cpp
    - Representation involved: n/a
    - Observable through: n/a — residual gap
- **Canonical definition:** "agreement" = field-by-field equality for exact fields, tolerance 1e-9 for the named float fields (timing.sampleRate, transforms translation/rotation), per battery-tester's comparison table.
- **Valid initial-state domain:** n/a — stateless per-sample comparison.
- **Property class:** Refinement/equivalence (cross-implementation), boundary/decoder correctness.
- **Concern role:** Current assurance property
- **Discovery source:** implementation observation (battery-tester harness already built and run)
- **Authority:** SPECIFIED
- **Authority basis:** OpenTrackIO v1.0.1 JSON schema (normative field names/types)
- **Claim nature:** Property
- **Lifecycle:** Enduring
- **Source evidence:** `battery-tester/run.py`, `battery-tester/README.md`, `battery-tester/adapters/{python,lean}_adapter.py`, `_CPP_FORK` integration in `run.py`
- **Confidence in intent:** high
- **Consequence if false:** A consumer of camdkit or opentrackio-cpp output receives metadata silently disagreeing with the normative schema (already observed once: `lens.focalLength` vs `lens.pinholeFocalLength`, fixed upstream PR#210)
- **Downstream dependencies:** Every claim about any single implementation's correctness relative to the Lean oracle
- **Preconditions:** Input sample is schema-valid JSON
- **Assumptions:** Lean oracle's decoder is itself correct (established separately by parser-verification proofs, not re-argued here)
- **Prioritization rationale:** Directly instantiates the user's stated goal (differential testing across the three implementations); already has a concrete, real bug found; cheap to extend (fixture corpus already generated)
- **Priority:** high
- **Disposition:** Approved
- **Evidence design (Phase 4A):**
  - Remaining uncertainty: whether the 3 implementations agree outside the already-run 4 canonical + 76 generated fixtures, and on the encode/roundtrip side
  - What passing would establish: no observed field disagreement across the exercised fixture corpus
  - Oracle authority: Lean decoder is formally proved sound/roundtrip-faithful against the v1.0.1 schema (`decodeSample_roundtrip`, decoder-soundness theorems)
  - Oracle independence: Lean model is independently authored from camdkit and opentrackio-cpp, no shared code
  - Shared-specification risk: all three read the same published schema text — a schema misreading shared by all three would not be caught by this comparison alone
  - Additional confidence this would add: extending the generated corpus and adding encode-side differential tests would close the current roundtrip gap
  - What important wrong implementation could still pass: one that agrees on these 18 fields but mishandles fields outside the comparison set (schema has more than 18 fields total — not full coverage)
  - Primary failure class detected: key-name/field-path/missing-field bugs (already demonstrated)
  - Important failure class still permitted: bugs in fields outside the 18-field comparison set; encode-path bugs; CBOR-input bugs (explicitly out of scope per battery-tester README)
- **Evidence coverage:**
  - decode agreement: camdkit vs Lean oracle -> differential test (`battery-tester/run.py --with-lean`)
  - decode agreement: opentrackio-cpp vs Lean oracle -> differential test (`battery-tester/run.py --with-lean`)
  - decode agreement: camdkit vs opentrackio-cpp -> differential test (`battery-tester/run.py`)
  - encode-side / full roundtrip agreement -> residual gap: no encode-side differential harness exists for camdkit or opentrackio-cpp
- **Evidence IDs:** EVID-001, EVID-002
- **Evidence summary:** differentially supported (decode-side, 18 fields, 80-fixture corpus); not yet evidenced for encode/roundtrip
- **Layering assessment:** complementary layers (differential harness + Lean oracle's own independent roundtrip proof), not assessed as independent beyond "no shared code" — no formal shared-bug-risk argument has been written
- **Residual gaps:**
  - Gap: no CI enforcement — harness is run manually, not gated in either repo's CI — Type: operational observability gap — Disposition: out of scope (CI wiring is implementation work, belongs to a LID-governed follow-up, not this MAPS pass)
  - Gap: encode-side/full-roundtrip differential coverage absent for camdkit and opentrackio-cpp — Type: evidence missing — Disposition: produce evidence
  - Gap: comparison limited to 18 of the schema's full field set — Type: evidence missing — Disposition: produce evidence (extend comparison fields)
  - Gap: no shared-bug-risk argument written for the three-way comparison — Type: evidence missing — Disposition: produce evidence (apply `checklists/differential-independence.md`)
- **Evidence-matrix row:** EVID-001, EVID-002 (see `evidence-matrix.md`)

---

### PROP-002: OpenCV → OpenTrackIO lens-parameter conversion correctness (as published)

- **Behavioral segment:** camdkit `docs/arrows/optical-characteristics.md`; `opentrackio-proof/opencv_opentrackio_proofs/`
- **Claim:** The published SMPTE RIS conversion formulas (principal-point offset, 8 distortion-coefficient scalings) are the unique values making the OpenCV and OpenTrackIO pixel-projection pipelines agree for all normalised input coordinates, and no tested wrong variant of these formulas is consistent.
- **Quantifiers in the claim:** for all real-valued `x'', y''` (principal point); for all `r` / all `(x', y')` (distortion, per polynomial degree); "no tested wrong variant" = the 40 mutation-test theorems specifically, not an exhaustive claim over all possible variants.
- **Claim dimensions:**
  - principal-point conversion (1D and 2D)
  - distortion coefficient conversion (radial + tangential, whole-polynomial)
  - known-wrong-variant rejection (mutation tests)
- **Implementation / representation surface:**
  - Claim dimension: principal-point conversion
    - Implemented/enforced by: `PrincipalPointConversion.lean`
    - Representation involved: exact-real Lean proof
    - Observable through: `lake build` (proof checked by Lean kernel)
  - Claim dimension: distortion coefficient conversion
    - Implemented/enforced by: `DistortionConversion.lean`
    - Representation involved: exact-real Lean proof
    - Observable through: `lake build`
  - Claim dimension: known-wrong-variant rejection
    - Implemented/enforced by: `MutationTests.lean` (40 theorems)
    - Representation involved: exact-real Lean proof
    - Observable through: `lake build`
- **Canonical definition:** "agree" = pixel-coordinate equality per the consistency equation in `opentrackio-proof-summary.md § 3.1`.
- **Valid initial-state domain:** n/a — pure mathematical claim, not a stateful system.
- **Property class:** Functional correctness, numeric correctness.
- **Concern role:** Current assurance property
- **Discovery source:** protocol/external specification (SMPTE RIS OTI-CVX paper)
- **Authority:** SPECIFIED
- **Authority basis:** SMPTE RIS "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters," corrected 2025-09-02 (`docs/OpenCV_to_OpenTrackIO.pdf`)
- **Claim nature:** Property
- **Lifecycle:** Enduring
- **Source evidence:** `opencv_opentrackio_proofs/PrincipalPointConversion.lean`, `DistortionConversion.lean`, `MutationTests.lean`; `docs/proof-map.md`
- **Confidence in intent:** high
- **Consequence if false:** Systematic pixel-registration error in every rendered frame using OpenCV-derived calibration
- **Downstream dependencies:** PROP-003 (pipeline equivalence) builds on these conversions
- **Preconditions:** nonzero image dimensions (`w ≠ 0`, `w_shader ≠ 0`)
- **Assumptions:** the SMPTE RIS paper's formulas are themselves the intended behavior (see PROP-004 for the one part of this where that assumption is in live doubt)
- **Prioritization rationale:** Central chokepoint for every downstream lens-geometry claim; already fully proved — registering it anchors the correctness-assurance summary in real, not aspirational, evidence
- **Priority:** high
- **Disposition:** Approved
- **Evidence design (Phase 4A):**
  - Remaining uncertainty: none for the formulas as published and formalized; see PROP-004 for the one open question about whether the published formula itself is physically correct
  - What passing would establish: the Lean kernel accepts the proofs, i.e. the stated biconditionals hold as pure mathematics
  - Oracle authority: Lean kernel type-checking against Mathlib axioms (no custom axioms introduced)
  - Oracle independence: n/a — formal proof, not a comparison against a second implementation
  - Shared-specification risk: the proof formalizes the paper's own stated formula; it cannot catch an error in the paper's own derivation (that is exactly PROP-004's open question)
  - Additional confidence this would add: none further justified for this claim as scoped — proof is complete
  - What important wrong implementation could still pass: n/a — this is a proof of the formula's uniqueness/necessity, not a test of an implementation
  - Primary failure class detected: any alternative formula failing the universal consistency condition
  - Important failure class still permitted: an implementation that misapplies the correct formula (that is PROP-001's concern, not this one)
- **Spec-clause trace:**
  - Spec clause: SMPTE RIS OTI-CVX conversion equations (principal point, radial/tangential coefficients)
  - Claim dimension: principal-point conversion; distortion coefficient conversion
  - Implementation/representation surface: Lean proof terms
  - Evidence observation: `lake build` exit 0 (3310 jobs per `opentrackio-proof-summary.md`)
- **Evidence coverage:**
  - principal-point conversion -> formal proof (`PrincipalPointConversion.lean`)
  - distortion coefficient conversion -> formal proof (`DistortionConversion.lean`)
  - known-wrong-variant rejection -> formal proof (`MutationTests.lean`, 40 theorems — this is the discrimination/anti-vacuity check for this property)
- **Evidence IDs:** EVID-003
- **Evidence summary:** formally proved (all three dimensions)
- **Layering assessment:** single layer (formal proof); mutation tests are itself the meta-evidence/discrimination layer for this property, not a second independent method
- **Residual gaps:** none currently identified for this property as scoped.
- **Evidence-matrix row:** EVID-003

---

### PROP-003: Full OpenCV/OpenLensIO pixel-level pipeline equivalence

- **Behavioral segment:** `opentrackio-proof/opencv_opentrackio_proofs/Pipeline/`
- **Claim:** Given all coefficient conversions from PROP-002 and `w_shader/w = fx` (resp. `h_shader/h = fy`), the OpenCV and OpenTrackIO full-pipeline x-pixel and y-pixel outputs each agree for all normalised inputs; conversely (given nonzero tangential coefficients), pixel agreement holds iff `w_shader/w = fx` (resp. `h_shader/h = fy`).
- **Quantifiers in the claim:** for all normalised x-coordinate and y-coordinate inputs; iff direction requires `p1 ≠ 0 ∨ p2 ≠ 0`.
- **Claim dimensions:**
  - x-pixel sufficiency (given conversions + aspect condition)
  - x-pixel iff (given conversions + nonzero tangential)
  - y-pixel equivalence (formalized — see below)
  - joint 2D (x and y together) equivalence
  - pure-radial case (`p1 = p2 = 0`) under mismatched `w_shader/w`
- **Implementation / representation surface:**
  - Claim dimension: x-pixel sufficiency / x-pixel iff
    - Implemented/enforced by: `Pipeline/PixelSufficiency.lean`, `Pipeline/PixelIff.lean`
    - Representation involved: exact-real Lean proof
    - Observable through: `lake build`
  - Claim dimension: y-pixel equivalence
    - Implemented/enforced by: `Pipeline/PixelSufficiencyY.lean`, `Pipeline/PixelIffY.lean`, `Pipeline/PixelIffHelpersY.lean`
    - Representation involved: exact-real Lean proof
    - Observable through: `lake build`
  - Claim dimension: joint 2D / pure-radial case
    - Implemented/enforced by: none — not formalized
    - Representation involved: n/a
    - Observable through: n/a — residual gaps below
- **Canonical definition:** "agree" = pixel equality per the full-pipeline definitions in `opentrackio-proof-summary.md § 4.1`.
- **Valid initial-state domain:** n/a.
- **Property class:** Functional correctness, refinement/equivalence.
- **Concern role:** Current assurance property
- **Discovery source:** protocol/external specification (derived from PROP-002's conversions plus the pipeline composition)
- **Authority:** SPECIFIED
- **Authority basis:** Same SMPTE RIS paper as PROP-002, for the x- and y-dimensions as formalized
- **Claim nature:** Property
- **Lifecycle:** Enduring
- **Source evidence:** `docs/proof-map.md § Full pipeline equivalence`; `docs/limitations.md § OpenCV ↔ OpenLensIO Conversion`
- **Confidence in intent:** high for x-dimension and y-dimension (both now formally proved)
- **Consequence if false:** Same class as PROP-002 (pixel misregistration), specifically for the full composed pipeline rather than isolated coefficient math
- **Downstream dependencies:** none currently registered
- **Preconditions:** `denominatorNonzero` free hypothesis (not derived from coefficient bounds — see residual gap)
- **Assumptions:** PROP-002's conversions hold; the paper's tangential consistency condition is physically correct (in live doubt — see PROP-004)
- **Prioritization rationale:** Directly downstream of the project's central proved result; the known gaps (y-symmetry, 2D joint, pure-radial) are explicitly flagged by the repo's own `limitations.md` as deliberately unformalized, not accidentally missed — worth tracking precisely rather than silently assuming covered
- **Priority:** medium
- **Disposition:** Approved (for the x-dimension and y-dimension, both proved); joint-2D and pure-radial residual gaps tracked explicitly rather than rolled into an overclaim
- **Evidence design (Phase 4A):**
  - Remaining uncertainty: whether the y-component, joint-2D, and pure-radial cases actually hold — `limitations.md` states the y-case "follows by inspection" but this has not been mechanically checked
  - What passing would establish (for the gaps, if pursued): that the claimed symmetry argument is not merely plausible but mechanically verified
  - Oracle authority: Lean kernel, same as PROP-002
  - Oracle independence: n/a
  - Shared-specification risk: same as PROP-002
  - Additional confidence this would add: a y-component proof would close a dimension the project's own docs flag as "expected, not planned"
  - What important wrong implementation could still pass: n/a for the proved x-dimension; for the unformalized dimensions, a subtly-wrong y-axis implementation would currently be undetected by any evidence in this register
  - Primary failure class detected (x-dimension): any implementation disagreeing on x-pixel output under the stated preconditions
  - Important failure class still permitted: y-axis-only errors; joint 2D errors; errors specific to the pure-radial case
- **Evidence coverage:**
  - x-pixel sufficiency -> formal proof (`PixelSufficiency.lean`)
  - x-pixel iff -> formal proof (`PixelIff.lean`)
  - y-pixel equivalence -> formal proof (`PixelSufficiencyY.lean`, `PixelIffY.lean`, `PixelIffHelpersY.lean`) — realized via LAPS handoff; see `docs/laps/y-pixel-equivalence/proof-review.md`
  - joint 2D equivalence -> residual gap: evidence missing ("not planned" per `limitations.md`, kept narrow rather than claimed)
  - pure-radial case -> residual gap: evidence missing ("not separately characterized" per `limitations.md`)
- **Evidence IDs:** EVID-003 (x-dimension, shared with PROP-002's proof base), EVID-006 (y-dimension, realized)
- **Evidence summary:** formally proved (x-dimension and y-dimension); not evidenced (joint-2D / pure-radial)
- **Layering assessment:** single layer (formal proof)
- **Residual gaps:**
  - Gap: no joint 2D pixel-equivalence theorem — Type: evidence missing — Disposition: defer — Owner/revisit trigger: the project's own docs state this is "not planned" by design; revisit only if a downstream consumer needs the joint interface
  - Gap: pure-radial case (`p1=p2=0`) under mismatched `w_shader/w` not characterized — Type: evidence missing — Disposition: defer — Owner/revisit trigger: revisit if a real zero-tangential-distortion lens calibration is submitted for verification
  - Gap: `denominatorNonzero` is a free hypothesis, not derived from coefficient bounds — Type: evidence missing — Disposition: produce evidence (bound derivation) / defer — Owner/revisit trigger: revisit if a working-radius-range bound becomes necessary for a specific lens family
- **Evidence-matrix row:** EVID-003, EVID-006

---

### PROP-004: SMPTE RIS paper tangential-conversion scaling is physically correct (SQ-CV-06)

- **Behavioral segment:** `opentrackio-proof/opencv_opentrackio_proofs/DistortionConversion.lean` vs `DistortionConversionCorrected.lean`
- **Claim:** The SMPTE RIS paper's stated tangential consistency condition (`δx_cv = δx_oti`, yielding `q1 = p1/F², q2 = p2/F²`) correctly describes how a real OpenCV-calibrated lens's tangential distortion should convert to OpenTrackIO/OpenLensIO coefficients.
- **Quantifiers in the claim:** for all lenses with nonzero tangential distortion (`p1 ≠ 0 ∨ p2 ≠ 0`).
- **Claim dimensions:** n/a — single external-correctness claim about the source specification itself.
- **Implementation / representation surface:**
  - Implemented/enforced by: n/a — this is a claim about the external SMPTE RIS paper, not about code in these repos
  - Representation involved: the paper's own coordinate-map derivation
  - Observable through: independent confirmation against a reference implementation or lens-rendering ground truth (not yet performed); `battery-tester/opencv_cross_check/` exists but is explicitly self-authored on both sides, not independent confirmation
- **Canonical definition:** "physically correct" = matches what a real calibrated lens with tangential distortion actually requires for correct undistortion, as would be confirmed by rendering against ground truth.
- **Valid initial-state domain:** n/a.
- **Property class:** Numeric correctness / external specification correctness.
- **Concern role:** External assumption
- **Discovery source:** MAPS domain-reasoning inference surfaced during formalization (recorded in opentrackio-proof's own `docs/specification-questions.md` as SQ-CV-06, prior to this MAPS pass)
- **Authority:** INFERRED
- **Authority basis:** inference only — a mechanically-proved alternative derivation (`DistortionConversionCorrected.lean`) exists alongside the paper's own stated formula, and the two disagree on the power of F; neither is confirmed authoritative
- **Claim nature:** External assumption
- **Lifecycle:** Enduring (this is a standing correctness question about the spec, not a migration)
- **Source evidence:** `docs/specification-questions.md` SQ-CV-06; `docs/laps/tangential-conversion-physical-fix/`; `DistortionConversionCorrected.lean`, `Pipeline/PixelIffCorrected.lean`
- **Confidence in intent:** low (this is precisely the open question)
- **Consequence if false:** Any implementation that followed the paper's formula as-published converts tangential distortion incorrectly for lenses with nonzero tangential coefficients, with no implementation-level test currently positioned to catch it
- **Downstream dependencies:** PROP-003's x-pixel iff theorem rests on the paper's (unconfirmed) formula; if SQ-CV-06 resolves toward the corrected version, PROP-003's `w_shader/w = fx` condition would not actually be required
- **Preconditions:** nonzero tangential distortion coefficients
- **Assumptions:** none further — this property exists specifically to avoid assuming the paper is correct without saying so
- **Prioritization rationale:** User explicitly asked this be registered; it is load-bearing for every downstream pixel-equivalence claim involving tangential distortion, and currently has zero independent evidence either way
- **Priority:** high
- **Disposition:** Awaiting intent confirmation. Outreach already performed: this exact question was emailed to James Uren (Mo-Sys, james@mo-sys.com) on 2026-08-15, including the `opencv_openlensio_full_pipeline_pixel_iff` reduction-to-`F=1` argument — a hand-derived corollary of that proved theorem together with its `hF_eq` hypothesis (independently re-verified during a MAPS audit pass: exact, no edge case missed), not itself a separately stated Lean theorem; no response recorded as of this MAPS pass. Freshness: verified as of 2026-08-15 (date of outreach) — revisit on maintainer response.
- **Evidence design (Phase 4A):**
  - Remaining uncertainty: which of the two mechanically-consistent alternatives (paper's `q=p/F²` vs corrected `q=p/F`) matches real lens behavior
  - What passing would establish: n/a until an independent oracle is identified — no evidence method has been selected yet because the oracle question itself is unresolved
  - Oracle authority: neither candidate oracle (the paper itself; this repo's own corrected derivation) is independent of the dispute — both are hypotheses, not yet external confirmation
  - Oracle independence: `opencv_cross_check/` fails independence (both sides authored by this repository) — explicitly documented as such in its own README
  - Shared-specification risk: total — this is exactly a dispute about the specification itself
  - Additional confidence this would add: none selectable yet
  - What important wrong implementation could still pass: n/a — evidence method not yet selected
  - Primary failure class detected: n/a
  - Important failure class still permitted: n/a
- **Evidence coverage:** n/a — single-instance claim; see Residual gaps (no dimension to discharge independently of the claim itself).
- **Evidence IDs:** none
- **Evidence summary:** no realized evidence — open question, correctly left open rather than evidenced by either Lean file alone
- **Layering assessment:** n/a
- **Residual gaps:**
  - Gap: SMPTE RIS paper's tangential conversion power-of-F is unconfirmed against ground truth — Type: specification ambiguity — Disposition: reconcile specification (already raised with Mo-Sys/James Uren by email 2026-08-15; alternatively obtain independent reference-rendering confirmation) — Owner/revisit trigger: revisit on maintainer response (none received as of this pass) or on independent confirmation from outside this repository
- **Evidence-matrix row:** none yet

---

### PROP-005: Converted lens coefficients are consumed in the direction the proofs establish (SQ-CV-07, D-U/U-D)

- **Behavioral segment:** OpenTrackIO `lens.distortion[].model` field semantics; `opentrackio-proof/opencv_opentrackio_proofs/Pipeline/`
- **Claim:** A real OpenTrackIO consumer that receives lens coefficients converted via the proved OpenCV→OpenTrackIO formulas applies them in the direction (U→D vs D→U) those formulas were actually derived for, consistent with — or overriding — the schema's stated default (`"Brown-Conrady D-U"`).
- **Quantifiers in the claim:** for any OpenTrackIO consumer processing a sample whose lens coefficients were produced via this conversion.
- **Claim dimensions:** n/a — single claim about producer/consumer direction convention.
- **Implementation / representation surface:**
  - Implemented/enforced by: n/a — no code in these repos asserts or enforces which direction a converted-coefficient producer should declare
  - Representation involved: `lens.distortion[].model` schema field; this repository's own parser already implements the documented default correctly for decode purposes (`LensDecoder.lean:150,167-168`, `LensModel.lean:7,68`) — that part is not in question
  - Observable through: not currently observable — no producer/consumer pair in these repos exercises this convention end-to-end
- **Canonical definition:** "the direction the proofs establish" = U→D coordinate-conjugacy, per `docs/specification-questions.md` SQ-CV-07.
- **Valid initial-state domain:** n/a.
- **Property class:** Compatibility / external specification correctness.
- **Concern role:** External assumption
- **Discovery source:** MAPS domain-reasoning inference surfaced during formalization (recorded as SQ-CV-07 prior to this MAPS pass)
- **Authority:** INFERRED
- **Authority basis:** inference only — the schema's documented default is opposite to what this repository's own pipeline theorems prove; no producer-side convention is documented or confirmed
- **Claim nature:** External assumption
- **Lifecycle:** Enduring
- **Source evidence:** `docs/specification-questions.md` SQ-CV-07; `docs/limitations.md § Pipeline theorems prove same-direction (U→D) conjugacy`
- **Confidence in intent:** low
- **Consequence if false:** A consumer applies converted coefficients in the schema-default direction (D→U) while they were actually derived U→D, silently producing incorrect undistortion with no error raised
- **Downstream dependencies:** none currently registered in this pass
- **Preconditions:** lens coefficients were produced via this repository's proved conversion formulas
- **Assumptions:** none further
- **Prioritization rationale:** User explicitly asked this be registered; silent-failure consequence (no error raised) makes it high-consequence despite currently being purely theoretical (no producer/consumer pair in these repos exercises it)
- **Priority:** medium
- **Disposition:** Awaiting intent confirmation. Outreach already performed: raised with James Uren (Mo-Sys, james@mo-sys.com) by email on 2026-08-15, as a follow-up in the same SQ-CV-06 thread; no response recorded as of this MAPS pass. Freshness: verified as of 2026-08-15 (date of outreach) — revisit on maintainer response.
- **Evidence design (Phase 4A):**
  - Remaining uncertainty: whether real producers are expected to set `model = "Brown-Conrady U-D"` explicitly, treat the schema default as advisory, or supply a genuinely-fitted D→U model instead
  - What passing would establish: n/a — no evidence method selected; this is a producer-convention question, not yet a testable implementation claim
  - Oracle authority: n/a — no authoritative source currently resolves this
  - Oracle independence: n/a
  - Shared-specification risk: total — same specification silence drives the whole question
  - Additional confidence this would add: none selectable yet
  - What important wrong implementation could still pass: n/a
  - Primary failure class detected: n/a
  - Important failure class still permitted: n/a
- **Evidence coverage:** n/a — single-instance claim; see Residual gaps.
- **Evidence IDs:** none
- **Evidence summary:** no realized evidence — open question
- **Layering assessment:** n/a
- **Residual gaps:**
  - Gap: producer/consumer direction convention for converted coefficients is unresolved by the spec — Type: specification ambiguity — Disposition: reconcile specification (already raised with Mo-Sys/James Uren by email 2026-08-15) — Owner/revisit trigger: revisit on maintainer response (none received as of this pass)
- **Evidence-matrix row:** none yet

---

### PROP-006: OpenTrackIO v1.0.1 schema text, as consulted, is current and normative

- **Behavioral segment:** cross-cutting — all three implementations and the Lean model
- **Claim:** The OpenTrackIO v1.0.1 JSON schema text consulted by this project (spot-checked against ris-pub.smpte.org and against camdkit's tracked `src/test/resources/classic/subschemas/lens.json`) is the current, normative schema all three implementations should conform to.
- **Quantifiers in the claim:** at time of spot-check; not continuously monitored.
- **Claim dimensions:** n/a — single external-currency claim.
- **Implementation / representation surface:**
  - Implemented/enforced by: n/a — external system (ris-pub.smpte.org publication), not controlled by this project
  - Representation involved: published schema JSON/PDF
  - Observable through: manual comparison (already performed once, per SQ-CV-07's investigation note)
- **Canonical definition:** n/a.
- **Valid initial-state domain:** n/a.
- **Property class:** Compatibility.
- **Concern role:** External assumption
- **Discovery source:** direct user statement / implementation observation (schema is the shared foundation all three implementations and the Lean model reference)
- **Authority:** SPECIFIED
- **Authority basis:** ris-pub.smpte.org published schema, manually confirmed verbatim against camdkit's tracked copy as of the SQ-CV-07 investigation
- **Claim nature:** External assumption
- **Lifecycle:** Enduring, but freshness-sensitive — the schema can be revised upstream
- **Source evidence:** `docs/specification-questions.md` SQ-CV-07 (manual verification note)
- **Confidence in intent:** high at time of check; unmonitored since
- **Consequence if false:** every property in this register that cites "the schema" as authority is only as current as the last manual check
- **Downstream dependencies:** PROP-001, PROP-002, PROP-005
- **Preconditions:** none
- **Assumptions:** none further
- **Prioritization rationale:** Foundational — every other property's Authority basis ultimately traces here; cheap to re-check periodically
- **Priority:** low (stable historically; cheap to re-verify, not urgent)
- **Disposition:** Approved, with Freshness tracked explicitly rather than assumed permanent
- **Evidence design (Phase 4A):**
  - Remaining uncertainty: whether the schema has changed since the last manual check
  - What passing would establish: no drift since last verification
  - Oracle authority: the published schema itself is authoritative by definition
  - Oracle independence: n/a — this is a freshness check, not a differential comparison
  - Shared-specification risk: n/a
  - Additional confidence this would add: a periodic re-check would catch upstream schema drift before it silently invalidates downstream properties
  - What important wrong implementation could still pass: n/a
  - Primary failure class detected: upstream schema drift
  - Important failure class still permitted: n/a
- **Evidence coverage:** n/a — single-instance claim; see Residual gaps.
- **Evidence IDs:** none (manual verification only, not yet a tracked EVID record)
- **Evidence summary:** manually verified (not formally tracked as an EVID record this pass)
- **Layering assessment:** n/a
- **Residual gaps:**
  - Gap: no periodic re-verification process exists — Type: external verification unavailable or missing — Disposition: manual/operational verification — Owner/revisit trigger: re-check when any of PROP-001/002/005 shows unexplained divergence, or at a fixed cadence if one is adopted
- **Evidence-matrix row:** none yet

## In-run Concern Classification

Normalized per `docs/claim-validation.md § 11`: resolved registered/retired/merged rows have been removed now that their disposition lives in `§ Register` or `system-assurance-map.md` directly. Only genuinely unresolved concerns, standing accepted assumptions, and open design questions remain below.

| Phase 1 concern | Concern role | Disposition | Detail |
|---|---|---|---|
| TLA+ proofs for the OpenTrackIO protocol (user's stated goal) | design question / design gap | tracked outside register | No state machine/temporal behavior is yet defined anywhere in the three repos; user chose to defer rather than force a candidate — revisit when a concrete protocol-level state/ordering/temporal behavior is named |
| OpenCV pinhole/distortion calibration convention is externally correct | external assumption | tracked outside register — accepted as standard | Not independently investigated; low novelty, standard external convention; revisit only if evidence suggests otherwise |
| nlohmann JSON parses per RFC 8259 | external assumption | tracked outside register — accepted as standard | Third-party library correctness, not investigated by this project; revisit only if evidence suggests otherwise |

## Pending user reconciliation

| Property ID | Authority | Claim (short) | Why MAPS believes it might matter |
|---|---|---|---|
| PROP-004 | INFERRED | SMPTE RIS paper's tangential conversion scaling (F vs F²) is physically correct | Two mechanically-consistent, mutually exclusive formulas exist; neither is confirmed against ground truth; affects every downstream pixel-equivalence claim for lenses with tangential distortion |
| PROP-005 | INFERRED | Converted coefficients are consumed in the direction the proofs establish, despite the schema's opposite-direction default | Silent-failure risk (no error raised); currently purely theoretical since no producer/consumer pair in these repos exercises it, but load-bearing if/when one does |
