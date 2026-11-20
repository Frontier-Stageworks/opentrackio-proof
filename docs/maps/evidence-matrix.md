# Evidence Matrix

Phase 4B artifact for the OpenTrackIO protocol assurance effort. Builds on Phase 4A fields recorded inline in `property-register.md`.

## Matrix

### PROP-001: Cross-implementation decode-field agreement

- **Evidence-design source:** `property-register.md § PROP-001 § Evidence design`
- **Additional evidence:** justified — see EVID-004, EVID-005 below for the two gaps worth active work; field-set expansion beyond 18 fields concluded not justified at current priority (see `§ Properties with no active evidence work`)
- **Claim type:** implementation equivalence (3-way decode agreement)
- **Consequence if false:** silent metadata disagreement reaching a render pipeline
- **Formalizability:** high for the Lean side (already proved separately); differential comparison is the only method that reaches camdkit and opentrackio-cpp directly
- **Executable oracle quality:** strong — Lean oracle is a formally-verified decoder, not a heuristic
- **Available reference implementation:** Lean oracle (`opentrackio_parser/`), exercised via `adapters/lean_adapter.py`
- **Reference kind / provenance:** proved formal model, exercised through a generated-runner adapter
- **Reference authority basis:** theorem (decoder soundness + roundtrip proofs)
- **Reference independence / shared-bug assessment:** camdkit (Python, SMPTE RIS org), opentrackio-cpp (C++, Mo-Sys), Lean oracle (this repository) — three different authors, three different languages, no shared decode code. All three share only the published schema text as a common input (see Shared-specification risk). See `§ Differential-testing entries requiring extra scrutiny` below for the full independence row.
- **Shared-specification risk:** all three read the same v1.0.1 schema; a misreading all three share in the same way (none currently known) would not be caught by this comparison
- **Reference freshness:** current as of the 2026-05-19 battery-tester reports
- **Production / model correspondence risk:** low for the Lean↔production comparison (direct field comparison, not a simplified model); the existing key-name bug is direct evidence the method works
- **Primary direct-evidence method:** differential testing
- **Supporting direct evidence:** formal proof (Lean oracle's own decoder-soundness/roundtrip theorems, EVID-003)
- **Enforcement mechanisms:** none
- **Meta-evidence / discrimination challenge:** the harness's own comparison-verdict logic (PASS/DIVERGE/MISSING) is property-tested (`battery-tester/tests/test_properties.py`) — this validates the harness itself, not the protocol implementations; no mutation/reintroduction challenge has been run against the implementations' decoders directly
- **Risk/assumption treatment:** none beyond the shared-specification risk noted above
- **Evidence purpose (per method above):** property support (differential agreement); the one real divergence found (`lens.pinholeFocalLength`) also served as fault discrimination and is now regression/change-detection context for that specific field
- **Claim-surface coverage:** see `property-register.md § PROP-001 § Implementation / representation surface`
- **Spec-clause trace:** n/a — field names/types traced directly via the schema, not a separate clause-numbering scheme
- **Generator-domain integrity:** Claim domain: all valid v1.0.1 samples. Generated domain: 4 canonical fixtures + 76-fixture parametric corpus (translation ±100m, rotation ±179.999°, 5 sample rates, timecode boundaries, epoch 0 through realistic timestamps, 4 sensor resolutions, 6 focal lengths, presence/absence of 4 optional fields). Excluded classes: CBOR input, fields outside the 18-field intersection. Why excluded: out of scope per battery-tester's stated design. Authority for exclusion: battery-tester README, accepted as a deliberate scope choice, not silently narrowed. Coverage consequence: bugs in excluded classes are not caught by this evidence.
- **Numeric/tolerance basis:** Generated numeric domain: see above. Tolerance: 1e-9 for float fields (sampleRate, translation, rotation), exact for integer/string/enum fields. Tolerance basis: battery-tester README comparison table. Behavior outside tested domain: unknown.
- **Roundtrip/equivalence semantics:** Input representation: canonical JSON fixture. Output representation: per-implementation internal sample value, reduced to the 18-field TSV. Information that must survive: the 18 named fields' semantic values. Allowed canonicalization: none specified beyond stated tolerances. Equivalence relation: field-by-field equality/tolerance, not whole-object equality. Intentional information loss: everything outside the 18 fields.
- **Negative/boundary isolation:** n/a — this is an agreement check, not a rejection-path test; MISSING entries are the closest analog (expected for fields the fixture intentionally omits) and are distinguished from DIVERGE in the harness's verdict logic.
- **Structural-enforcement assessment:** n/a — not a boundedness/resource-safety claim.
- **Quantifier coverage check:** yes — the claim's "for every fixture in the exercised corpus" is exactly what the harness iterates over; the claim does not assert universality beyond the exercised corpus, and the register's wording reflects that (sampled evidence, not "for all valid samples unconditionally").
- **Claim-dimension discharge check:** yes — all 4 dimensions in `property-register.md § PROP-001` have an entry in its Evidence coverage field (3 covered by differential test, 1 recorded as residual gap, not silently excluded).
- **Rationale:** Differential testing is the only method that reaches camdkit and opentrackio-cpp as black boxes without requiring their own formal models; the Lean oracle supplies the independent, authoritative third column that lets the harness attribute a divergence to a specific implementation rather than leaving it as "two disagree, which is right?"
- **Downstream workflow / tool:** `battery-tester/run.py` (existing); EVID-004/EVID-005 below for the two active gaps
- **Wording check:** n/a — claim is already scoped to "the exercised fixture corpus," not stated as universal
- **Vacuity check:** generator reachability confirmed (76-fixture corpus deliberately targets boundary values per field); the harness has already demonstrated discrimination by finding a real bug (`lens.pinholeFocalLength`), which is stronger evidence of discrimination than a synthetic mutation test would be
- **Counterexample reconciliation:** n/a — no currently-failing evidence for this property (the one known divergence is explained, attributed, and fixed upstream)
- **Repository-history citation:** the `lens.pinholeFocalLength` bug and its upstream fix (PR#210) are cited as historical regression context for this property's evidence purpose — permitted under the opt-in exception (prior production bug, regression-test anchor), not used to manufacture an oracle
- **Evidence IDs:** EVID-001, EVID-002, EVID-003 (realized); EVID-004, EVID-005 (planned)
- **Layering assessment:** independent layers — see `§ Differential-testing entries requiring extra scrutiny` for the shared-bug-risk argument
- **Residual-gap source:** `property-register.md § PROP-001 § Residual gaps`
- **Correctness-assurance.md row:** `correctness-assurance.md § 2` (Current Properties)

### PROP-002 / PROP-003: OpenCV↔OpenTrackIO conversion and pipeline equivalence

- **Evidence-design source:** `property-register.md § PROP-002 / PROP-003 § Evidence design`
- **Additional evidence:** none justified for PROP-002 (proof complete as scoped); justified for PROP-003's y-pixel dimension — see EVID-006 below; not justified at current priority for joint-2D and pure-radial dimensions (see `§ Properties with no active evidence work`)
- **Claim type:** universal semantic invariant (biconditional algebraic claims over exact reals)
- **Consequence if false:** systematic pixel-registration error
- **Formalizability:** high — pure algebra over `ℝ`, within Mathlib's existing tactic set
- **Executable oracle quality:** n/a — formal proof, not an executable test oracle
- **Available reference implementation:** n/a
- **Reference kind / provenance:** n/a
- **Reference authority basis:** n/a
- **Reference independence / shared-bug assessment:** n/a
- **Shared-specification risk:** the proof formalizes the SMPTE RIS paper's own stated formula; it is authoritative for "is this formula internally forced by its own consistency condition," not for "is the paper's formula itself physically correct" (that gap is exactly PROP-004)
- **Reference freshness:** n/a
- **Production / model correspondence risk:** n/a — no production code claim here, pure specification-formula claim
- **Primary direct-evidence method:** formal proof
- **Supporting direct evidence:** none
- **Enforcement mechanisms:** none
- **Meta-evidence / discrimination challenge:** 40 mutation-test theorems (`MutationTests.lean`) — every tested wrong variant (wrong offset form, wrong F-power, coefficient swaps) is shown degenerate or inconsistent; this is the discrimination/anti-vacuity check for PROP-002
- **Risk/assumption treatment:** none beyond the shared-specification risk noted above
- **Evidence purpose (per method above):** property support
- **Claim-surface coverage:** see `property-register.md § PROP-002/003 § Implementation / representation surface`
- **Spec-clause trace:** Spec clause: SMPTE RIS OTI-CVX conversion equations. Claim dimension: principal-point + distortion conversion (PROP-002); x-pixel pipeline equivalence (PROP-003). Implementation/representation surface: Lean proof terms. Evidence observation: `lake build` exit 0.
- **Generator-domain integrity:** n/a — formal proof over all reals in domain, not sampled.
- **Numeric/tolerance basis:** n/a — exact real arithmetic, no tolerance.
- **Roundtrip/equivalence semantics:** n/a.
- **Negative/boundary isolation:** n/a.
- **Structural-enforcement assessment:** n/a.
- **Quantifier coverage check:** yes — theorem statements are literally `∀` over the claimed domain; Lean's kernel checks this is not vacuous (hypotheses are satisfiable; see Vacuity check).
- **Claim-dimension discharge check:** yes for PROP-002 (all 3 dimensions covered by proof); yes for PROP-003 (x-dimension covered, y/joint-2D/pure-radial recorded as residual gaps, not silently excluded).
- **Rationale:** Formal proof is the correct method for a universal algebraic claim with a bounded, well-specified proof surface and high failure consequence — exactly the profile `docs/evidence-selection.md` recommends it for.
- **Downstream workflow / tool:** already realized; no handoff needed for PROP-002 or PROP-003's x-dimension
- **Wording check:** yes — `property-register.md`'s claim wording for both properties states the quantifiers explicitly (not bare "always"); satisfied.
- **Vacuity check:** hypotheses are satisfiable (nonzero image dimensions is a normal case, not vacuous); mutation tests confirm the theorem discriminates against wrong variants rather than holding trivially.
- **Counterexample reconciliation:** n/a — no failing evidence.
- **Repository-history citation:** the earlier SMPTE RIS paper's buggy formula (missing `−w_shader/2` term) is cited as the historical regression the mutation-test suite's `buggy_principal_point_conversion_inconsistent` theorem guards against — permitted under the opt-in exception.
- **Evidence IDs:** EVID-003 (realized, PROP-002 + PROP-003 x-dimension); EVID-006 (realized, PROP-003 y-dimension)
- **Layering assessment:** single layer (formal proof) with an internal discrimination layer (mutation tests)
- **Residual-gap source:** `property-register.md § PROP-002 § Residual gaps` (none); `§ PROP-003 § Residual gaps` (joint-2D, pure-radial, denominator bound)
- **Correctness-assurance.md row:** `correctness-assurance.md § 2`

## Differential-testing entries requiring extra scrutiny

| Property ID | Reference kind/provenance | Authority basis | Independence/shared-bug assessment | Freshness | Checklist run? |
|---|---|---|---|---|---|
| PROP-001 | Lean oracle, proved formal model (not a second "implementation" in the ordinary sense) | Decoder-soundness + roundtrip theorems, checked by Lean kernel | Three distinct authors/orgs (SMPTE RIS camdkit, Mo-Sys opentrackio-cpp, this project's Lean model), three languages, no shared decode code. Shared risk is limited to the one thing all three necessarily share: the published schema text itself. No shared helper libraries, no shared generated code, no common author between any pair. | Current as of 2026-05-19 battery-tester reports; not continuously re-run | Partial — authorship/language/code independence assessed directly above; `checklists/differential-independence.md`'s full checklist has not been formally stepped through item-by-item as a separate exercise |

## Properties with no active evidence work (Deferred / Accept risk)

| Property ID | Gap type (cause) | Gap disposition | Why no active evidence |
|---|---|---|---|
| PROP-003 (joint 2D pixel equivalence) | Evidence missing | Defer | Project's own `limitations.md` already states this is "not planned"; x-theorem + informal symmetry argument judged sufficient; low exposure (no consumer currently needs the joint interface) |
| PROP-003 (pure-radial case, `p1=p2=0`) | Evidence missing | Defer | Low exposure — real lenses with tracked tangential distortion are the common case this effort targets; revisit only if a zero-tangential-distortion lens calibration is actually submitted |
| PROP-003 (`denominatorNonzero` bound derivation) | Evidence missing | Defer | Remaining uncertainty is partly a domain question (what coefficient bounds count as "physically realistic") not yet resolved by anyone, not purely a proof-cost question; forcing a handoff now would hand LAPS an ill-posed target |
| PROP-001 (field-set expansion beyond 18 fields) | Evidence missing | Defer | The 18 fields were a deliberate intersection choice; no specific known bug motivates expansion yet, and expanding requires nontrivial new per-field harness work across both camdkit and opentrackio-cpp — lower value per unit cost than the two active gaps (EVID-004, EVID-005) |
| PROP-004 (SQ-CV-06) | Specification ambiguity | Reconcile specification | Not an evidence-method gap — the oracle question itself (which formula is physically correct) has no evidence method until the ambiguity resolves externally |
| PROP-005 (SQ-CV-07) | Specification ambiguity | Reconcile specification | Same as above — producer/consumer convention question, not resolvable by evidence this project can produce alone |

## Properties where additional evidence was concluded not justified

| Property ID | Existing evidence relied on | Reason additional evidence isn't justified |
|---|---|---|
| PROP-002 | `PrincipalPointConversion.lean`, `DistortionConversion.lean`, `MutationTests.lean` | The formula-uniqueness claim, as scoped (does the published formula follow from the consistency condition, and are known wrong variants rejected), is fully and exactly discharged by the existing proof; no further evidence would reduce remaining uncertainty about this specific claim |
| PROP-006 (schema currency) | Manual spot-check recorded in `docs/specification-questions.md` SQ-CV-07 | A one-time differential/property-test method doesn't apply to "is the schema text current" — the only meaningful further evidence is periodic re-verification, already recorded as the property's own residual gap (manual/operational verification), not a new evidence method to design |

## Evidence records

### EVID-001: Canonical-fixture 3-way differential run

- **Supports properties / dimensions:** PROP-001 (camdkit vs Lean, opentrackio-cpp vs Lean, camdkit vs opentrackio-cpp)
- **Lifecycle state:** realized
- **Direct-evidence method:** differential comparison
- **Target:** production code (camdkit, opentrackio-cpp) + formal model (Lean oracle)
- **Purpose:** property support; fault discrimination (found the `lens.pinholeFocalLength` bug)
- **Execution state:** Exists: yes. Collected/discovered by runner: yes (`battery-tester/run.py`). Runnable: yes. Executed: yes (dated reports `battery-tester-2026-05-16-*.txt`, `battery-tester-2026-05-19-*.txt`). Passing: 17/18 fields agree; 1 expected DIVERGE (explained, upstream-fixed). Fresh: as of 2026-05-19. CI-enforced: no.
- **Oracle / decision criterion:** field-by-field equality/tolerance across the three adapters' outputs
- **Oracle authority:** Lean adapter is backed by proved decoder-soundness/roundtrip theorems
- **Oracle independence / shared-bug risk:** see `§ Differential-testing entries requiring extra scrutiny`
- **Shared-specification risk:** all three share the published schema text
- **Reference kind / provenance (differential):** Lean formal model, exercised via generated runner
- **Reference authority basis:** theorem
- **Reference independence / shared-bug assessment:** independent authorship/language/code, per above
- **Reference freshness:** 2026-05-19
- **Artifact / result:** `battery-tester/battery-tester-2026-05-16-{1,2,3}.txt`, `battery-tester-2026-05-19-{1,2}.txt`
- **Freshness:** verified as of 2026-05-19
- **Important blind spot:** encode-side/roundtrip behavior of camdkit and opentrackio-cpp; fields outside the 18-field intersection; CBOR input
- **Linked enforcement mechanisms:** none
- **Meta-evidence:** harness's own verdict logic is property-tested (`tests/test_properties.py`), separate from this record (see EVID-002's note)
- **Risk/assumption treatment:** none

### EVID-002: Generated-corpus 3-way differential run + harness property tests

- **Supports properties / dimensions:** PROP-001 (same three dimensions, extended coverage via boundary-value corpus)
- **Lifecycle state:** realized
- **Direct-evidence method:** differential comparison (corpus) + property-based test (harness verdict logic)
- **Target:** production code (camdkit, opentrackio-cpp) + formal model (Lean oracle); harness's own comparison logic
- **Purpose:** property support (corpus); fault discrimination / gap confirmation (harness property tests validate PASS/DIVERGE/MISSING verdict correctness, not the protocol implementations themselves)
- **Execution state:** Exists: yes. Collected/discovered by runner: yes (`generate_fixtures.py`, `run.py --generated`, `pytest tests/test_properties.py`). Runnable: yes. Executed: yes. Passing: yes (per README's documented behavior). Fresh: fixtures regenerated on demand, not committed to git. CI-enforced: no.
- **Oracle / decision criterion:** same as EVID-001, over 76 boundary/mid-range/optional-field-combination fixtures
- **Oracle authority:** same as EVID-001
- **Oracle independence / shared-bug risk:** same as EVID-001
- **Shared-specification risk:** same as EVID-001
- **Reference kind / provenance (differential):** same as EVID-001
- **Reference authority basis:** theorem
- **Reference independence / shared-bug assessment:** same as EVID-001
- **Reference freshness:** regenerated per-run, not version-pinned
- **Artifact / result:** `battery-tester/generate_fixtures.py`, `fixtures/generated/*.json` (76 files), `tests/test_properties.py`
- **Freshness:** current (regenerated on demand)
- **Important blind spot:** same as EVID-001, plus: corpus is parametric/boundary-targeted, not randomly fuzzed — a bug reachable only by an unanticipated combination outside the designed parameter grid would not be caught
- **Linked enforcement mechanisms:** none
- **Meta-evidence:** `tests/test_properties.py` is itself the discrimination check for the harness's verdict logic (confirms PASS/DIVERGE/MISSING classification and aggregate counts are computed correctly) — this is meta-evidence about the test harness, not about the protocol implementations
- **Risk/assumption treatment:** none

### EVID-003: Lean proof corpus (conversion, pipeline, mutation tests)

- **Supports properties / dimensions:** PROP-002 (all 3 dimensions); PROP-003 (x-pixel sufficiency, x-pixel iff)
- **Lifecycle state:** realized
- **Direct-evidence method:** formal proof
- **Target:** formal model (exact-real Lean definitions of the SMPTE RIS conversion formulas)
- **Purpose:** property support; fault discrimination (mutation tests)
- **Execution state:** Exists: yes. Collected/discovered by runner: yes (`lake build`). Runnable: yes. Executed: yes, `lake build` exits 0 (3310 jobs per `opentrackio-proof-summary.md`). Passing: yes — all listed theorems type-check. Fresh: current. CI-enforced: not confirmed in this pass (no CI config inspected).
- **Oracle / decision criterion:** Lean kernel type-checking against Mathlib, no custom axioms
- **Oracle authority:** mathematical proof of the stated biconditionals
- **Oracle independence / shared-bug risk:** n/a — proof, not a second implementation
- **Shared-specification risk:** formalizes the SMPTE RIS paper's own stated formula (see PROP-004 for the one place this risk is live and unresolved)
- **Reference kind / provenance:** n/a
- **Reference authority basis:** n/a
- **Reference independence / shared-bug assessment:** n/a
- **Reference freshness:** n/a
- **Artifact / result:** `opencv_opentrackio_proofs/PrincipalPointConversion.lean`, `DistortionConversion.lean`, `MutationTests.lean`, `Pipeline/PixelSufficiency.lean`, `Pipeline/PixelIff.lean`
- **Freshness:** current
- **Important blind spot:** y-dimension (covered separately by EVID-006, not by this record), joint-2D and pure-radial case (still open PROP-003 residual gaps); whether the formalized formula is itself physically correct (PROP-004)
- **Linked enforcement mechanisms:** none
- **Meta-evidence:** 40 mutation-test theorems in `MutationTests.lean`
- **Risk/assumption treatment:** none

### EVID-004: Encode-side / full-roundtrip differential harness (camdkit, opentrackio-cpp) — planned

- **Supports properties / dimensions:** PROP-001 (encode-side / full roundtrip agreement dimension)
- **Lifecycle state:** planned
- **Direct-evidence method:** differential comparison
- **Target:** production code (camdkit, opentrackio-cpp)
- **Purpose:** property support (closing the one dimension PROP-001 currently leaves as a residual gap)
- **Execution state:** Exists: no. Collected/discovered by runner: n/a. Runnable: n/a. Executed: n/a. Passing: n/a. Fresh: n/a. CI-enforced: n/a.
- **Oracle / decision criterion:** `decode(encode(x)) ≡ canonicalize(x)` agreement against the Lean oracle's own proved `encodeSample_roundtrip`, extended to camdkit/opentrackio-cpp's own encode paths if they expose one
- **Oracle authority:** Lean's `encodeSample_roundtrip` theorem
- **Oracle independence / shared-bug risk:** same independence profile as EVID-001/002
- **Shared-specification risk:** same as EVID-001
- **Reference kind / provenance:** proved formal model
- **Reference authority basis:** theorem
- **Reference independence / shared-bug assessment:** same as EVID-001
- **Reference freshness:** n/a — not yet built
- **Artifact / result:** none yet — see `evidence-handoff.md`
- **Freshness:** n/a
- **Important blind spot:** n/a until built
- **Linked enforcement mechanisms:** none
- **Meta-evidence:** a mutation/reintroduction check against the encode path (e.g. reintroducing the historical key-name bug on the encode side) would be the natural discrimination challenge, to be specified in the handoff
- **Risk/assumption treatment:** none

### EVID-005: Field-set expansion — explicitly not planned

- **Supports properties / dimensions:** PROP-001 (would extend coverage beyond the current 18 fields)
- **Lifecycle state:** retired (concluded not justified at current priority; see `§ Properties with no active evidence work`)
- **Direct-evidence method:** n/a — not selected
- **Target:** n/a
- **Purpose:** n/a
- **Execution state:** n/a
- **Oracle / decision criterion:** n/a
- **Oracle authority:** n/a
- **Oracle independence / shared-bug risk:** n/a
- **Shared-specification risk:** n/a
- **Reference kind / provenance:** n/a
- **Reference authority basis:** n/a
- **Reference independence / shared-bug assessment:** n/a
- **Reference freshness:** n/a
- **Artifact / result:** n/a
- **Freshness:** n/a
- **Important blind spot:** fields outside the 18-field intersection remain untested by this effort
- **Linked enforcement mechanisms:** none
- **Meta-evidence:** n/a
- **Risk/assumption treatment:** accept risk — recorded in `correctness-assurance.md § 6`

### EVID-006: Y-pixel equivalence formal proof — realized

- **Supports properties / dimensions:** PROP-003 (y-pixel equivalence dimension)
- **Lifecycle state:** realized
- **Direct-evidence method:** formal proof
- **Target:** formal model — `opencv_openlensio_full_pipeline_pixel_sufficiency_y` and `opencv_openlensio_full_pipeline_pixel_iff_y` in new files `Pipeline/PixelSufficiencyY.lean`, `Pipeline/PixelIffHelpersY.lean`, `Pipeline/PixelIffY.lean`
- **Purpose:** property support — closes the dimension the project's own `limitations.md` previously left as "expected, not proved"
- **Execution state:** Exists: yes. Collected/discovered by runner: yes (`lake build`). Runnable: yes. Executed: yes. Passing: yes — full project `lake build` succeeds, 3316 jobs. Fresh: current. CI-enforced: no (same as all other evidence in this matrix — no CI wiring exists in this repository).
- **Oracle / decision criterion:** Lean kernel type-checking, same proof shape as the existing x-theorem, mechanically mirrored with the axis-swap correspondence confirmed against `whole_tangential_field_2d_iff` and `principal_point_conversion_2d_iff` before any proof code was written
- **Oracle authority:** same mathematical derivation as PROP-003's x-dimension
- **Oracle independence / shared-bug risk:** n/a — proof, not a second implementation
- **Shared-specification risk:** same as PROP-002/003 — uses the paper's as-published tangential formula (`q1=p1/F²,q2=p2/F²`), not the corrected alternative, per the LAPS handoff's explicit instruction; SQ-CV-06's open question is therefore still live and applies equally to this new theorem
- **Reference kind / provenance:** n/a
- **Reference authority basis:** n/a
- **Reference independence / shared-bug assessment:** n/a
- **Reference freshness:** n/a
- **Artifact / result:** `docs/laps/y-pixel-equivalence/proof-review.md`; theorems in `Pipeline/PixelSufficiencyY.lean`, `Pipeline/PixelIffHelpersY.lean`, `Pipeline/PixelIffY.lean`
- **Freshness:** current
- **Important blind spot:** does not close the joint-2D or pure-radial gaps (still deferred, unchanged); still inherits SQ-CV-06's open question about whether the underlying tangential formula is itself physically correct
- **Linked enforcement mechanisms:** none
- **Meta-evidence:** realized — `MutationTestsY.lean`, two y-axis mutation-theorem categories (wrong F-power, coefficient swap), both discriminate correctly (materially wrong variants proved inconsistent)
- **Risk/assumption treatment:** none
