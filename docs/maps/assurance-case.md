# Assurance Case

Structured traceability counterpart to `correctness-assurance.md` for the OpenTrackIO protocol interoperability effort.

## Traces

### PROP-001: Cross-implementation decode-field agreement

```text
Property (property-register.md):
  camdkit, opentrackio-cpp, and the Lean oracle agree on 18 comparison fields
  for valid OpenTrackIO v1.0.1 samples, within stated tolerances.
        ↓
Preconditions / initial-state domain:
  Input is schema-valid OpenTrackIO v1.0.1 JSON. n/a — stateless per-sample.
        ↓
Assumptions:
  - PROP-006: consulted schema text is current and normative.
  - Lean oracle's own decoder is correct (established by PROP-002/parser proofs, not re-argued here).
        ↓
Claim dimensions:
  - camdkit vs Lean oracle
  - opentrackio-cpp vs Lean oracle
  - camdkit vs opentrackio-cpp
  - encode-side / full roundtrip agreement
        ↓
Evidence mapped to claim dimensions (evidence-matrix.md):
  - camdkit vs Lean oracle -> EVID-001, EVID-002, differential comparison, battery-tester reports. Purpose: property support; fault discrimination (found the pinholeFocalLength bug).
  - opentrackio-cpp vs Lean oracle -> EVID-001, EVID-002, same method. Purpose: property support.
  - camdkit vs opentrackio-cpp -> EVID-001, EVID-002, same method. Purpose: property support.
  - encode-side / full roundtrip agreement -> residual gap (see below); EVID-004 planned.
        ↓
Enforcement mechanisms:
  none
        ↓
Meta-evidence / discrimination:
  Harness's own verdict logic (PASS/DIVERGE/MISSING) is property-tested
  (tests/test_properties.py) — validates the harness, not the implementations
  directly. The implementations' own discrimination evidence is the real
  key-name bug the harness already found and attributed.
        ↓
Risk/assumption treatment:
  none beyond the shared-specification risk noted in correctness-assurance.md § 4
        ↓
Current support:
  Differentially supported over 80 exercised fixtures (4 canonical + 76
  generated); not a claim of universal agreement over all valid samples.
        ↓
Residual gaps:
  - Description: no encode-side/full-roundtrip differential coverage for camdkit or opentrackio-cpp
    Gap type: evidence missing
    Gap disposition: produce evidence (EVID-004 planned, evidence-handoff.md)
  - Description: comparison limited to 18 of the schema's full field set
    Gap type: evidence missing
    Gap disposition: defer (EVID-005, concluded not justified at current priority)
  - Description: no CI enforcement of the harness in either repository
    Gap type: operational observability gap
    Gap disposition: out of scope
  - Description: no formal shared-bug-risk checklist walkthrough performed (only a direct independence argument)
    Gap type: evidence missing
    Gap disposition: defer
        ↓
Disposition / next action:
  Authority: SPECIFIED
  Authority basis: OpenTrackIO v1.0.1 JSON schema
  Claim nature: Property
  Lifecycle: Enduring
  Disposition: Approved
  Evidence summary: differentially supported (decode-side); not evidenced (encode/roundtrip)
  Layering assessment: independent layers (three distinct authors/orgs/languages, no shared decode code); shared risk limited to common schema text
  Freshness: verified as of 2026-05-19
  Correctness-assurance.md section: § 3.1
```

### PROP-002: OpenCV → OpenTrackIO conversion correctness

```text
Property (property-register.md):
  The published principal-point and distortion-coefficient conversion formulas
  are the unique values making the OpenCV/OpenTrackIO pipelines pixel-consistent,
  and no tested wrong variant is also consistent.
        ↓
Preconditions / initial-state domain:
  Nonzero image dimensions (w ≠ 0, w_shader ≠ 0). n/a — pure math claim.
        ↓
Assumptions:
  - The SMPTE RIS paper's stated consistency condition is the correct criterion to formalize (not itself in doubt — PROP-004 concerns only the tangential-scaling sub-formula, not this criterion).
        ↓
Claim dimensions:
  - principal-point conversion (1D and 2D)
  - distortion coefficient conversion (radial + tangential, whole-polynomial)
  - known-wrong-variant rejection
        ↓
Evidence mapped to claim dimensions (evidence-matrix.md):
  - principal-point conversion -> EVID-003, formal proof, PrincipalPointConversion.lean. Purpose: property support.
  - distortion coefficient conversion -> EVID-003, formal proof, DistortionConversion.lean. Purpose: property support.
  - known-wrong-variant rejection -> EVID-003, formal proof, MutationTests.lean (40 theorems). Purpose: fault discrimination / meta-evidence.
        ↓
Enforcement mechanisms:
  none
        ↓
Meta-evidence / discrimination:
  40 mutation-test theorems; each tested wrong variant shown degenerate or
  inconsistent. Historical regression guard: buggy_principal_point_conversion_inconsistent
  proves the earlier published formula (missing the -w_shader/2 term) is
  mathematically inconsistent.
        ↓
Risk/assumption treatment:
  none
        ↓
Current support:
  Formally proved, complete as scoped. Lake build exits 0 (3310 jobs).
        ↓
Residual gaps:
  none currently identified for this property as scoped.
        ↓
Disposition / next action:
  Authority: SPECIFIED
  Authority basis: SMPTE RIS "Conversion of OpenCV to OpenTrackIO" paper, corrected 2025-09-02
  Claim nature: Property
  Lifecycle: Enduring
  Disposition: Approved
  Evidence summary: formally proved (all 3 dimensions)
  Layering assessment: single layer (formal proof) with internal discrimination layer (mutation tests)
  Freshness: current
  Correctness-assurance.md section: § 3.2
```

### PROP-003: Full OpenCV/OpenLensIO pixel-level pipeline equivalence

```text
Property (property-register.md):
  Given PROP-002's conversions and w_shader/w = fx, OpenCV and OpenTrackIO
  x-pixel outputs agree for all normalised inputs; conversely (nonzero
  tangential coefficients), agreement holds iff w_shader/w = fx.
        ↓
Preconditions / initial-state domain:
  denominatorNonzero free hypothesis (not derived from coefficient bounds). n/a — pure math claim.
        ↓
Assumptions:
  - PROP-002's conversions hold.
  - The paper's tangential consistency condition is physically correct (in live doubt — PROP-004).
        ↓
Claim dimensions:
  - x-pixel sufficiency
  - x-pixel iff
  - y-pixel equivalence
  - joint 2D equivalence
  - pure-radial case (p1=p2=0)
        ↓
Evidence mapped to claim dimensions (evidence-matrix.md):
  - x-pixel sufficiency -> EVID-003, formal proof, Pipeline/PixelSufficiency.lean. Purpose: property support.
  - x-pixel iff -> EVID-003, formal proof, Pipeline/PixelIff.lean. Purpose: property support.
  - y-pixel equivalence -> EVID-006, formal proof, Pipeline/PixelSufficiencyY.lean + Pipeline/PixelIffY.lean. Purpose: property support. Realized via LAPS handoff.
  - joint 2D equivalence -> residual gap; deferred, not planned.
  - pure-radial case -> residual gap; deferred.
        ↓
Enforcement mechanisms:
  none
        ↓
Meta-evidence / discrimination:
  Shares PROP-002's mutation-test suite for the underlying conversions on the x-side;
  the y-dimension has its own discrimination suite (MutationTestsY.lean: wrong-F-power
  and coefficient-swap categories, both confirmed to correctly reject the wrong variant).
        ↓
Risk/assumption treatment:
  joint-2D / pure-radial: deferred, not accepted risk without cause — each has an explicit
  gap type and disposition (see below), not a bare "accepted risk."
        ↓
Current support:
  Formally proved for both the x-dimension and the y-dimension (docs/laps/y-pixel-equivalence/
  proof-review.md). The y-proof confirmed the axis-swap correspondence by direct inspection
  of whole_tangential_field_2d_iff before writing any Lean code, rather than relying on the
  repository's prior informal "expected by inspection" symmetry claim.
        ↓
Residual gaps:
  - Description: no joint 2D pixel-equivalence theorem
    Gap type: evidence missing
    Gap disposition: defer (project's own docs call this "not planned")
  - Description: pure-radial case under mismatched w_shader/w (or h_shader/h) not characterized
    Gap type: evidence missing
    Gap disposition: defer
  - Description: denominatorNonzero is a free hypothesis, not derived from coefficient bounds
    Gap type: evidence missing
    Gap disposition: defer (ill-posed until a domain question — "realistic" coefficient bounds — is resolved)
        ↓
Disposition / next action:
  Authority: SPECIFIED
  Authority basis: same SMPTE RIS paper as PROP-002, for both the x- and y-dimensions as formalized
  Claim nature: Property
  Lifecycle: Enduring
  Disposition: Approved (x-dimension and y-dimension; joint-2D and pure-radial gaps tracked explicitly, not rolled into the claim)
  Evidence summary: formally proved (x-dimension, y-dimension); not evidenced (joint-2D / pure-radial)
  Layering assessment: single layer (formal proof)
  Freshness: current
  Correctness-assurance.md section: § 3.3
```

### PROP-004: SMPTE RIS paper tangential-conversion physical correctness (SQ-CV-06)

```text
Property (property-register.md):
  The SMPTE RIS paper's stated tangential consistency condition correctly
  describes how a real OpenCV-calibrated lens's tangential distortion should
  convert to OpenTrackIO/OpenLensIO coefficients.
        ↓
Preconditions / initial-state domain:
  Nonzero tangential distortion (p1 ≠ 0 ∨ p2 ≠ 0). n/a otherwise.
        ↓
Assumptions:
  none further — this property exists specifically to avoid silently assuming the paper is correct.
        ↓
Claim dimensions:
  n/a — single-instance claim about the external specification itself.
        ↓
Evidence mapped to claim dimensions (evidence-matrix.md):
  Primary: none selected — no evidence method chosen because the oracle
  question itself (which of two mechanically-consistent formulas is
  physically correct) is unresolved. Supporting: none.
        ↓
Enforcement mechanisms:
  none
        ↓
Meta-evidence / discrimination:
  n/a — opencv_cross_check/ exists but is explicitly self-authored on both
  sides, documented in its own README as not independent confirmation.
        ↓
Risk/assumption treatment:
  explicit assumption, currently unconfirmed in either direction
        ↓
Current support:
  No realized evidence. Correctly left open rather than evidenced by either
  of this repository's own two candidate derivations.
        ↓
Residual gaps:
  - Description: SMPTE RIS paper's tangential conversion power-of-F is unconfirmed against ground truth
    Gap type: specification ambiguity
    Gap disposition: reconcile specification (raise with OpenTrackIO/SMPTE RIS maintainers, or obtain independent reference-rendering confirmation)
        ↓
Disposition / next action:
  Authority: INFERRED
  Authority basis: inference only — a mechanically-proved alternative derivation exists alongside the paper's own formula, disagreeing on the power of F
  Claim nature: External assumption
  Lifecycle: Enduring
  Disposition: Awaiting intent confirmation
  Evidence summary: no realized evidence
  Layering assessment: n/a
  Freshness: n/a
  Correctness-assurance.md section: § 3.4, § 6.2
```

### PROP-005: Converted-coefficient consumption direction (SQ-CV-07)

```text
Property (property-register.md):
  A real OpenTrackIO consumer applies converted lens coefficients in the
  direction (U→D) the proofs establish, consistent with or overriding the
  schema's stated default ("Brown-Conrady D-U").
        ↓
Preconditions / initial-state domain:
  Lens coefficients were produced via this repository's proved conversion formulas.
        ↓
Assumptions:
  none further
        ↓
Claim dimensions:
  n/a — single-instance claim about producer/consumer convention.
        ↓
Evidence mapped to claim dimensions (evidence-matrix.md):
  Primary: none selected — no producer/consumer pair in these repos exercises
  this convention end-to-end; this repository's own parser already implements
  the documented D-U default correctly for decode purposes, which is not in
  question here.
        ↓
Enforcement mechanisms:
  none
        ↓
Meta-evidence / discrimination:
  n/a
        ↓
Risk/assumption treatment:
  explicit assumption, currently unconfirmed in either direction
        ↓
Current support:
  No realized evidence — open question.
        ↓
Residual gaps:
  - Description: producer/consumer direction convention for converted coefficients is unresolved by the spec
    Gap type: specification ambiguity
    Gap disposition: reconcile specification (raise with OpenTrackIO maintainers)
        ↓
Disposition / next action:
  Authority: INFERRED
  Authority basis: inference only — schema's documented default is opposite to what this repository's pipeline theorems prove
  Claim nature: External assumption
  Lifecycle: Enduring
  Disposition: Awaiting intent confirmation
  Evidence summary: no realized evidence
  Layering assessment: n/a
  Freshness: n/a
  Correctness-assurance.md section: § 3.4, § 6.2
```

### PROP-006: OpenTrackIO schema currency/normativity

```text
Property (property-register.md):
  The OpenTrackIO v1.0.1 schema text consulted by this project is the
  current, normative schema all three implementations should conform to.
        ↓
Preconditions / initial-state domain:
  none
        ↓
Assumptions:
  none further
        ↓
Claim dimensions:
  n/a — single-instance currency claim.
        ↓
Evidence mapped to claim dimensions (evidence-matrix.md):
  Primary: manual verification (spot-check against ris-pub.smpte.org and
  camdkit's tracked lens.json, performed during the SQ-CV-07 investigation).
  Supporting: none.
        ↓
Enforcement mechanisms:
  none
        ↓
Meta-evidence / discrimination:
  n/a
        ↓
Risk/assumption treatment:
  none beyond the freshness gap below
        ↓
Current support:
  Manually verified as current at time of check; not continuously monitored.
        ↓
Residual gaps:
  - Description: no periodic re-verification process exists
    Gap type: external verification unavailable or missing
    Gap disposition: manual/operational verification
        ↓
Disposition / next action:
  Authority: SPECIFIED
  Authority basis: ris-pub.smpte.org published schema, manually confirmed verbatim against camdkit's tracked copy
  Claim nature: External assumption
  Lifecycle: Enduring, freshness-sensitive
  Disposition: Approved
  Evidence summary: manually verified (not a tracked EVID record this pass)
  Layering assessment: n/a
  Freshness: verified as of the SQ-CV-07 investigation; not re-checked since
  Correctness-assurance.md section: § 5.1
```

## Coverage check

| Property ID | Has assurance-case trace? | Has correctness-assurance.md claim row? | Discrepancy? |
|---|---|---|---|
| PROP-001 | yes | yes (§ 3.1) | none |
| PROP-002 | yes | yes (§ 3.2) | none |
| PROP-003 | yes | yes (§ 3.3) | none |
| PROP-004 | yes | yes (§ 3.4) | none |
| PROP-005 | yes | yes (§ 3.4) | none |
| PROP-006 | yes | yes (§ 5.1) | none |
