# OpenTrackIO Protocol Interoperability Correctness / Assurance Document

**Version:** 1
**Scope:** Cross-implementation correctness of the OpenTrackIO v1.0.1 protocol and its companion OpenLensIO v1.0.1 lens model, across three repositories: `opentrackio-proof` (Lean 4 formal verification + `battery-tester` differential harness), `ris-osvp-metadata-camdkit` (Python reference implementation), `opentrackio-cpp` (Mo-Sys C++ implementation).
**Repository:** `opentrackio-proof` (this document's canonical home)
**Companion documents:** `property-register.md`, `evidence-matrix.md`, `assurance-case.md`, `system-assurance-map.md`

# 1. Purpose and Scope

This document states what can currently be claimed about whether `ris-osvp-metadata-camdkit` and `opentrackio-cpp` correctly and interoperably implement the OpenTrackIO/OpenLensIO protocols, and what the proofs in `opentrackio-proof` do and do not establish about that.

**"Correctness" here means:** (a) the published OpenCV→OpenTrackIO lens-calibration conversion formulas are the mathematically unique values a consistent conversion requires; (b) the three independent parser implementations (camdkit, opentrackio-cpp, the Lean model) agree on decoded field values for the protocol's comparison-relevant fields; (c) the Lean parser model's own encode/decode roundtrip and decoder-soundness properties hold.

**This document explicitly does NOT claim:**
- an end-to-end theorem connecting a parsed OpenTrackIO sample to semantically correct rendered pixel output (no such theorem exists; see § 6);
- that the SMPTE RIS paper's published tangential-distortion conversion formula is itself physically correct (open question, § 5.3, § 6);
- that converted lens coefficients are consumed in the direction the proofs establish rather than the schema's stated opposite-direction default (open question, § 5.3, § 6);
- byte-level JSON parsing correctness for any of the three implementations;
- CI enforcement of any evidence described here — all current evidence was run manually, not gated in either repository's CI;
- any TLA+ -backed temporal/state-machine property — none exists yet in any of the three repositories (recorded as an open design gap, not a claim).

No end-to-end machine-checked proof exists linking parsed protocol data to correct rendered output. Where a sizeable test or proof volume exists, this document says what was specifically measured, not a coverage fraction — requirement-to-test traceability has not been measured for camdkit's or opentrackio-cpp's own unit test suites.

# 2. System Model

See `system-assurance-map.md` for the full map. Summary:

- **Segments:** parser/decoder (all three repos); OpenCV↔OpenLensIO lens-parameter conversion (opentrackio-proof only, math-level); OpenLensIO Brown-Conrady semantic pipeline (opentrackio-proof only, math-level).
- **Trust boundary:** untrusted wire JSON → three independent decoders.
- **Reference/formal model:** the Lean model in `opentrackio-proof` is the one formally-verified component; camdkit and opentrackio-cpp are production parsers evaluated against it by differential comparison, not by a proved correspondence.
- **External dependencies:** OpenTrackIO v1.0.1 JSON schema (ris-pub.smpte.org); SMPTE RIS "Conversion of OpenCV to OpenTrackIO" paper; OpenLensIO v1.0.1 specification; nlohmann JSON (C++ dependency).

# 3. Correctness / Assurance Claims

## 3.1 Cross-implementation decode-field agreement

**Precondition(s):** input is schema-valid OpenTrackIO v1.0.1 JSON.
**Canonical definition(s):** "agreement" = field-by-field equality (exact fields) or equality within 1e-9 tolerance (float fields), over the 18 battery-tester comparison fields.
**Valid initial-state domain:** n/a — stateless per-sample comparison.

| Claim | Property Type | Evidence IDs | Current support |
|---|---|---|---|
| camdkit, opentrackio-cpp, and the Lean oracle agree on 18 comparison fields, over 4 canonical + 76 generated fixtures | Equivalence | EVID-001, EVID-002 | Differentially supported over the exercised fixture corpus; not a claim of universal agreement over all valid samples |

**Property being asserted:** the three implementations agree on these fields for arbitrary valid OpenTrackIO v1.0.1 samples.
**Evidence produced:** agreement confirmed over 80 specific fixtures (4 canonical + 76 parametric/boundary-targeted), not an exhaustive or randomly-fuzzed sample of the input space.

| Dimension | Discharge |
|---|---|
| camdkit vs Lean oracle | differential test (EVID-001, EVID-002) |
| opentrackio-cpp vs Lean oracle | differential test (EVID-001, EVID-002) |
| camdkit vs opentrackio-cpp | differential test (EVID-001, EVID-002) |
| encode-side / full roundtrip agreement | residual gap (EVID-004, planned) |

**Coverage facts:**
- Input domain: 4 canonical fixtures (complete/recommended × static/dynamic) + 76 generated fixtures targeting boundary values across translation, rotation, sample rate, timecode, timestamp, sensor resolution, focal length, and optional-field presence/absence.
- Reference independence: three distinct authors/organizations (SMPTE RIS camdkit, Mo-Sys opentrackio-cpp, this project's Lean model), three languages, no shared decode code; shared risk limited to the common schema text (see § 4).
- Production path: direct comparison of each implementation's own decode output, not a simplified model.
- Model scope: Lean oracle covers the full 18-field comparison set exercised by the harness.
- Quantifier coverage: the claim is scoped to "the exercised fixture corpus," matching what the evidence actually covers.
- Discrimination result: the harness has already found and attributed a real defect (camdkit's `lens.focalLength` vs normative `lens.pinholeFocalLength`), which is direct evidence the comparison discriminates rather than passing vacuously.

**Accepted / Rejected — fixture corpus boundary:**
- Accepted: 80 fixtures spanning canonical examples and parametric boundary values across the 18 comparison fields.
- Rejected (out of scope): CBOR input; fields outside the 18-field intersection; randomly fuzzed input outside the designed parameter grid.

## 3.2 OpenCV → OpenTrackIO lens-parameter conversion correctness

**Precondition(s):** nonzero image dimensions (`w ≠ 0`, `w_shader ≠ 0`).
**Canonical definition(s):** "correct" = the published formula is the unique solution to the universal pixel-consistency equation (`system-assurance-map.md`, `proof-map.md`).
**Valid initial-state domain:** n/a — pure mathematical claim.

| Claim | Property Type | Evidence IDs | Current support |
|---|---|---|---|
| Published principal-point and distortion-coefficient conversion formulas are necessary and sufficient for pixel consistency | Equivalence (formula-level) | EVID-003 | Formally proved; complete as scoped |
| 40 tested wrong-formula variants are all shown degenerate or inconsistent | Equivalence (discrimination) | EVID-003 | Formally proved |

**Coverage facts:**
- Formalizability: pure algebra over `ℝ`, within Mathlib's existing tactic set; no custom axioms.
- Quantifier coverage: theorem statements are literal `∀`-quantified biconditionals over the claimed domain.
- Discrimination result: 40 mutation-test theorems confirm no tested wrong variant also satisfies the consistency condition.
- Historical regression: the earlier SMPTE RIS paper's own buggy formula (missing `−w_shader/2` term) is proved inconsistent (`buggy_principal_point_conversion_inconsistent`), guarding against reintroducing that specific historical error.

**Accepted / Rejected — formula scope:**
- Accepted: the formula's internal necessity/sufficiency relative to its own stated consistency condition.
- Rejected (out of scope here, see § 3.3 and § 5.3): whether the paper's tangential-conversion formula is itself physically correct.

## 3.3 Full OpenCV/OpenLensIO pixel-level pipeline equivalence

**Precondition(s):** all PROP-002 coefficient conversions hold; `denominatorNonzero` (free hypothesis, not derived from coefficient bounds).
**Lifecycle:** Enduring.

| Claim | Property Type | Evidence IDs | Current support |
|---|---|---|---|
| x-pixel outputs agree given conversions + `w_shader/w = fx` (sufficiency) | Equivalence | EVID-003 | Formally proved |
| x-pixel agreement ↔ `w_shader/w = fx`, given nonzero tangential coefficients | Equivalence | EVID-003 | Formally proved |
| y-pixel outputs agree given conversions + `h_shader/h = fy` (sufficiency) | Equivalence | EVID-006 | Formally proved |
| y-pixel agreement ↔ `h_shader/h = fy`, given nonzero tangential coefficients | Equivalence | EVID-006 | Formally proved |

| Dimension | Discharge |
|---|---|
| x-pixel sufficiency | formal proof (EVID-003) |
| x-pixel iff | formal proof (EVID-003) |
| y-pixel equivalence | formal proof (EVID-006) |
| joint 2D equivalence | residual gap — deferred, not planned (project's own docs call it unneeded beyond the x-theorem + symmetry argument) |
| pure-radial case (`p1=p2=0`) | residual gap — deferred |
| `denominatorNonzero` bound derivation | residual gap — deferred (domain question, not yet a well-posed proof target) |

**Coverage facts:**
- The y-pixel dimension, previously supported only by an informal symmetry argument in the project's own `limitations.md`, is now formally proved (`Pipeline/PixelSufficiencyY.lean`, `Pipeline/PixelIffY.lean`) via a LAPS handoff that confirmed the axis-swap correspondence by direct inspection of `whole_tangential_field_2d_iff` before writing any proof code, rather than by trusting the informal "by inspection" claim. See `docs/laps/y-pixel-equivalence/proof-review.md`.
- The y-proof uses the paper's as-published tangential conversion formula (`q1=p1/F², q2=p2/F²`), not the corrected alternative under investigation in § 3.4 — so SQ-CV-06's open question applies identically to both the x- and y-dimensions now.

**Accepted / Rejected — pipeline scope:**
- Accepted: x-pixel and y-pixel equivalence under the stated conversions and aspect condition.
- Rejected (not established): joint 2D, pure-radial case, and the physical correctness of the underlying tangential formula itself (§ 3.4).

## 3.4 External assumptions about the source specification (SQ-CV-06, SQ-CV-07)

**Precondition(s):** none — these are assumptions this project depends on but does not control.
**Lifecycle:** Enduring (standing questions about the external specification, not migrations).

| Claim | Property Type | Evidence IDs | Current support |
|---|---|---|---|
| SMPTE RIS paper's tangential conversion scaling (`q=p/F²`) is physically correct | External assumption | none | Open — INFERRED only; a mechanically-proved alternative (`q=p/F`) exists and the two are mutually exclusive |
| Converted coefficients are consumed in the direction the proofs establish (U→D), not the schema's stated default (D→U) | External assumption | none | Open — INFERRED only; no producer/consumer pair in these repos exercises this convention |

**Coverage facts:**
- Neither assumption has a currently-identified authoritative oracle; both require either an erratum from the OpenTrackIO/SMPTE RIS maintainers or independent confirmation against ground truth outside this project's own authorship. Both were raised with Mo-Sys (James Uren) by email on 2026-08-15; no response recorded as of this document's current revision.
- `battery-tester/opencv_cross_check/` is explicitly not independent confirmation for SQ-CV-06 — both sides are authored by this repository (documented as such in its own README).

**Accepted / Rejected:**
- Accepted: both questions are genuine, previously-undetected ambiguities in the external specification, each with a mechanically-proved alternative on record.
- Rejected: treating either ambiguity as resolved in either direction without external confirmation.

# 4. Structure of the Assurance Argument

| Evidence Layer | Catches | Does NOT Catch |
|---|---|---|
| Lean formal proof (conversion formulas, pipeline x-dimension, parser roundtrip/soundness) | Any formula violating its own stated consistency condition; any decoder violating type-carried structural invariants | Whether the formalized formula is itself physically correct (§ 3.4); byte-level JSON parsing; production-code correspondence |
| battery-tester 3-way differential (camdkit vs opentrackio-cpp vs Lean oracle) | Field-level decode disagreement between any pair of the three implementations, on the 18 exercised fields | Fields outside the 18-field intersection; encode-side/roundtrip behavior of camdkit/opentrackio-cpp; CBOR input |
| Mutation tests (`MutationTests.lean`, 40 theorems) | Plausible wrong-formula variants for the conversion math | Wrong variants not anticipated by the mutation set |

**Evidence independence note:** The differential layer and the Lean formal-proof layer are complementary and substantially independent — three different authors/organizations, three languages, no shared decode code (see `evidence-matrix.md § Differential-testing entries requiring extra scrutiny`). The one shared-bug risk across all layers is the published schema/specification text itself: a misreading or genuine ambiguity in the spec (as SQ-CV-06/SQ-CV-07 already demonstrate exists) would not be caught by agreement among implementations that all consulted the same source.

# 5. Assumptions

## 5.1 Specification currency

- The OpenTrackIO v1.0.1 schema text consulted (spot-checked against ris-pub.smpte.org and camdkit's tracked `lens.json`) is current and normative. Manually verified once (SQ-CV-07 investigation); not continuously monitored. See PROP-006.

## 5.2 External library / convention correctness

- OpenCV's pinhole/distortion calibration convention is as OpenCV documents it. Not independently investigated by this project; accepted as standard.
- nlohmann JSON (C++ dependency of `opentrackio-cpp`) parses per RFC 8259. Not independently investigated; accepted as standard.

## 5.3 Open specification questions (load-bearing)

- SMPTE RIS paper's tangential conversion scaling is physically correct (SQ-CV-06) — unresolved; see § 3.4, § 6.
- Converted coefficients are consumed in the proved direction, not the schema's default (SQ-CV-07) — unresolved; see § 3.4, § 6.

# 6. Residual Risks and Model Gaps

## 6.1 Cross-proof-area composition gap

No end-to-end theorem connects "a parsed OpenTrackIO sample" to "semantically correct rendered pixel output." The parser, OpenLensIO semantic, and OpenCV↔OpenTrackIO conversion proofs are each internally sound but proved independently of one another.

## 6.2 Unresolved specification ambiguities (PROP-004, PROP-005)

SQ-CV-06 and SQ-CV-07 are genuine open questions about the external specification, each with a mechanically-proved alternative on record and no independent confirmation either way. Any implementation of tangential-distortion conversion, or any consumer applying converted coefficients, is currently exposed to a silent (non-crashing) correctness risk from either ambiguity.

## 6.3 Production-model correspondence gap

The Lean model operates on an already-parsed `JsonValue` AST (not raw bytes) and is compared to camdkit/opentrackio-cpp only via the 18-field battery-tester comparison, not via a proved correspondence. Agreement across 80 fixtures is evidence of correspondence on those fields and fixtures, not a proof of correspondence in general.

## 6.4 Evidence maintenance gap

No evidence described in this document is CI-enforced. A future change to camdkit or opentrackio-cpp could silently break agreement with the Lean oracle without being caught until the harness is re-run manually.

## 6.5 Encode-side / roundtrip gap

Only decode-side agreement is differentially tested for camdkit and opentrackio-cpp. Encode-path correctness for these two implementations is untested by this effort (Lean's own encode/decode roundtrip is proved, but that says nothing about camdkit's or opentrackio-cpp's own encoders, if they have one).

## 6.6 No TLA+ work exists

The user's stated goal for this effort includes TLA+ proofs. No state machine, session model, or temporal/ordering property is currently defined in any of the three repositories. This is recorded as an open design gap (tracked in `property-register.md`'s Concern Classification ledger), not a property with a disposition — there is nothing yet to prove.

## 6.7 opentrackio-cpp has no independent LID map

opentrackio-cpp's own correctness is assessed only through its black-box JSON-in/JSON-out behavior via `dump_sample`, by agreed-upon user decision (not a LID bootstrap gap being silently ignored). No claim in this document depends on opentrackio-cpp's internal code paths.

# 7. Trusted Base

- **Lean 4 kernel + Mathlib** — every formal-proof claim (§ 3.2, § 3.3, parser decoder/roundtrip proofs) is only as trustworthy as Lean's kernel and the Mathlib axioms it builds on. No custom axioms were introduced.
- **`lake env lean --run` harness path** — the Lean adapter in battery-tester runs via this path rather than a compiled native binary, due to a documented Lean 4.29.0/Darwin 25.3.0 linker incompatibility (packaging limitation only, not a soundness gap per `docs/limitations.md`).
- **nlohmann JSON** — `opentrackio-cpp`'s JSON parsing dependency; its own correctness is an accepted external assumption (§ 5.2).
- **Python `json` module** — camdkit's and the battery-tester's own JSON parsing dependency; not independently investigated.
- **CPython runtime, C++20 toolchain** — standard language-runtime trust, not independently investigated.

# 8. Summary of Guarantees

- The published OpenCV→OpenTrackIO principal-point and distortion-coefficient conversion formulas are proved to be the unique values satisfying their own stated consistency condition, and 40 tested wrong variants are proved inconsistent or degenerate (§ 3.2 — formally proved, complete as scoped).
- The full x-pixel and y-pixel pipelines are each proved to agree between OpenCV and OpenTrackIO under the stated conversions and aspect condition (§ 3.3 — formally proved for both dimensions; the joint 2D and pure-radial cases remain open).
- camdkit, opentrackio-cpp, and the Lean oracle are differentially confirmed to agree on 18 named fields across 80 specific fixtures, with one historical divergence found, attributed, and fixed upstream (§ 3.1 — differentially supported over the exercised corpus, not a universal claim).
- Two specification-level questions (SQ-CV-06, SQ-CV-07) remain genuinely open and are explicitly not resolved by anything in this document (§ 3.4, § 6.2) — neither should be treated as settled in either direction.
- No claim in this document establishes end-to-end correctness from wire bytes to rendered pixel output, CI-enforced regression protection, or TLA+-backed temporal correctness (§ 6).

# 9. Correctness Claim Taxonomy

| Property Type | Definition | Primary Sections |
|---|---|---|
| Equivalence | Two independent implementations (or an implementation and a formula/model) agree | § 3.1, § 3.2, § 3.3 |
