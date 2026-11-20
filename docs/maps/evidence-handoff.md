# Evidence Handoff

Phase 7 artifact for the OpenTrackIO protocol assurance effort. None of the three repositories (`opentrackio-proof`, `ris-osvp-metadata-camdkit`, `opentrackio-cpp`) is LID-governed for the `battery-tester` harness specifically — camdkit has its own LID arrows for its production code, but the harness itself lives in `opentrackio-proof`, which has no LID map. This file is therefore the terminal MAPS deliverable for the entries below, per `docs/integrations/lid.md § MAPS → LID handoff`'s fallback rule.

## Gap disposition routing

| Property | Gap | Gap disposition | Block used below |
|---|---|---|---|
| PROP-001 | encode-side / full-roundtrip agreement | Produce evidence | Differential-test contract |
| PROP-001 | field-set expansion beyond 18 fields | Defer | No action scheduled |
| PROP-001 | no CI enforcement | Out of scope | No entry needed — noted in `property-register.md` only |
| PROP-001 | no formal shared-bug-risk checklist walkthrough | Defer | No action scheduled |
| PROP-003 | joint 2D pixel equivalence | Defer | No action scheduled |
| PROP-003 | pure-radial case (`p1=p2=0`) | Defer | No action scheduled |
| PROP-003 | `denominatorNonzero` bound derivation | Defer | No action scheduled |
| PROP-004 | SQ-CV-06 tangential physical correctness | Reconcile specification | Design-decision handoff |
| PROP-005 | SQ-CV-07 D-U/U-D direction | Reconcile specification | Design-decision handoff |
| PROP-006 | no periodic re-verification process | Manual/operational verification | Manual verification procedure |

## Differential-test contract

### PROP-001 — Differential-test contract: encode-side / full-roundtrip agreement

**Target:** `ris-osvp-metadata-camdkit`'s encode path (if one exists symmetric to its decoder) and `opentrackio-cpp`'s encode path (if `OpenTrackIOSample`/`OpenTrackIOProperties` expose one), compared against the Lean oracle's proved `encodeSample_roundtrip`.

**Reference kind / provenance:** Lean `opentrackio_parser/` encode/decode model, proved (`encodeSample_roundtrip` and the full chain of sub-encoder roundtrip theorems in `docs/proof-map.md § Encode/decode roundtrip`).

**Authority basis:** theorem (machine-checked roundtrip proof, OpenTrackIO v1.0.1 schema as the field-naming authority).

**Independence / shared-bug assessment:** same three-way independence already established for PROP-001's decode-side evidence (`evidence-matrix.md § Differential-testing entries requiring extra scrutiny`) — no new risk introduced by adding the encode direction, since it exercises the same three independently-authored codebases.

**Freshness:** n/a — not yet built.

**Shared-specification risk:** same as the decode-side comparison — all three share the published schema text.

**What's compared:** for each of a set of generated `Sample` values (reuse or extend `battery-tester/generate_fixtures.py`'s existing corpus): `decode(encode(x))` should recover `x` (or its canonical form) for each implementation independently, and cross-implementation, `camdkit.encode(x)` and `opentrackio-cpp.encode(x)` should each decode (by the Lean oracle) to the same semantic value as `x`.

**Roundtrip/equivalence semantics:** Input representation: an in-memory sample value (language-specific per implementation). Output representation: re-serialized JSON, then re-decoded. Information that must survive: the same 18 comparison fields already tracked by the decode-side harness (extending further is a separate, deferred concern — see `§ No action scheduled`). Allowed canonicalization: same tolerances as the decode-side comparison (1e-9 float, exact otherwise). Equivalence relation: field-by-field, not whole-JSON-text equality (key order, whitespace not claimed to be preserved). Intentional information loss: fields outside the 18-field set, exactly as already scoped for the decode-side harness.

**Shared-bug-risk assessment:** already covered by the existing three-way independence argument; no incremental risk from exercising the encode direction of the same three codebases.

**Fix/report scope:** a divergence here is evidence of an encode-path bug in whichever of camdkit/opentrackio-cpp disagrees with the Lean oracle (which is authoritative by proof for the roundtrip property) — report as a bug against that implementation's repository, the same way the existing `lens.pinholeFocalLength` decode-side bug was reported upstream (PR#210).

**Discrimination / anti-vacuity challenge:** reintroduce the historical `lens.pinholeFocalLength`/`lens.focalLength` key-name confusion on the encode side as a deliberate mutation (if camdkit's encoder can be made to emit the wrong key) and confirm the harness flags it — this directly tests whether the new encode-side comparison actually discriminates, using a known real defect class as the target.

**LID entry point:** n/a — no LID governs `battery-tester`; this specification is the terminal deliverable. If camdkit's own LID-governed encode path needs changes to support this (unlikely — this is additive test infrastructure in `battery-tester`, not a change to camdkit itself), that would separately enter camdkit's own LID Phase 5.

## Design-decision handoff

### PROP-004 — Design-decision handoff (reconciliation)

**Owner:** the user. **Already performed:** emailed to James Uren (Mo-Sys, james@mo-sys.com) on 2026-08-15, including the `opencv_openlensio_full_pipeline_pixel_iff` reduction-to-`F=1` argument and a reference to the machine-checked Lean proof plus the self-authored `opencv_cross_check` numerical check against a real camera calibration. No response recorded as of this MAPS pass — revisit on maintainer reply, or by commissioning independent reference-rendering confirmation if no reply arrives.

**Gap type:** specification ambiguity.

**Question to resolve:** does the SMPTE RIS paper's published tangential-distortion conversion (`q1=p1/F², q2=p2/F²`, zero factors of F on the OpenCV side of the consistency condition) correctly describe real-lens behavior, or is the corrected alternative derived in this repository (`q1=p1/F, q2=p2/F`, one factor of F) the physically correct one? These are mutually exclusive and both are mechanically proved internally consistent — the question is which matches reality, not which is self-consistent.

**Once a design exists:** once the maintainers issue an erratum, or an independent reference-rendering comparison is obtained, the resolved formula becomes PROP-004's Authority (SPECIFIED, with the erratum or confirmation as Authority basis), and PROP-003's x-pixel-iff theorem's `ws/w = fx` condition should be re-examined against `docs/limitations.md § 4.3`'s note that the corrected formula removes that condition entirely — this would need `property-register.md § PROP-003` updated accordingly, not left reading as a permanent requirement if it may be a formalization artifact of the as-published formula specifically.

**Not MAPS's call to make:** this is a correctness question about an external specification MAPS does not own or author; resolving it requires authority MAPS cannot generate — either the paper's own maintainers or empirical ground truth outside this repository.

### PROP-005 — Design-decision handoff (reconciliation)

**Owner:** the user. **Already performed:** raised with James Uren (Mo-Sys, james@mo-sys.com) by email on 2026-08-15, as a follow-up in the same thread as PROP-004's outreach. No response recorded as of this MAPS pass.

**Gap type:** specification ambiguity.

**Question to resolve:** when a producer emits lens coefficients converted via the proved OpenCV→OpenTrackIO formulas (which this repository's proofs establish only in the U→D, same-direction-conjugacy sense), should that producer explicitly set `lens.distortion[].model = "Brown-Conrady U-D"` to override the schema's stated default (`"Brown-Conrady D-U"`), should the documented default be understood as advisory rather than binding, or is a producer instead expected to supply a genuinely-fitted native D→U model rather than a coordinate-conjugate one?

**Once a design exists:** once the maintainers clarify the intended producer convention, this becomes a concrete, testable claim — e.g. "producers using this repository's conversion formulas MUST set `model` to X" — which would then get its own property-register entry with Authority: SPECIFIED, and could be checked by a straightforward static/schema check (does the emitted sample set the field correctly) rather than requiring new proof work.

**Not MAPS's call to make:** this is a producer-convention question about an external specification's silence; MAPS has no authority to declare the intended convention on the maintainers' behalf.

## Manual / non-automatable verification procedure

### PROP-006 — Manual verification procedure (not automatable)

**Owner:** whoever next touches any property in this register that cites the OpenTrackIO v1.0.1 schema as Authority basis (PROP-001, PROP-002, PROP-005) — most naturally, the person running the next MAPS maintenance pass.

**Procedure:**
1. Fetch the current schema text from ris-pub.smpte.org.
2. Diff it against the last-verified text (captured in `docs/specification-questions.md` SQ-CV-07's investigation note and against camdkit's tracked `src/test/resources/classic/subschemas/lens.json`).
3. If no diff: update this property's Freshness date in `property-register.md § PROP-006`. If a diff exists: flag every downstream property whose Authority basis cites the schema (PROP-001, PROP-002, PROP-005) for re-review before trusting their current Disposition.

**Recording:** record the check date directly in `property-register.md § PROP-006`'s Freshness field (e.g. "verified as of `<date>`"), per the opt-in exception for dates that are load-bearing for external-system freshness.

**Does not self-renew:** this verification is a point-in-time snapshot. It provides zero ongoing protection against a schema revision published the day after the check — there is no monitoring in place, only a manual trigger-on-touch process.

**If it fails:** if the schema has materially changed, this becomes a live design/specification question for whichever properties relied on the stale reading — route back to a MAPS Phase 2/6 pass to re-classify affected properties' Authority, not a silent artifact edit.

## No action scheduled

### PROP-001 — No action scheduled: field-set expansion beyond 18 fields

**Gap type:** evidence missing.
**Gap disposition:** Defer.
**Owner / sign-off:** n/a (deferred, not accepted risk).
**Revisit trigger:** a specific bug report or consumer need surfaces in a field outside the current 18-field comparison set.

**Disposition:** defer.
**Basis:** the 18 fields were a deliberate intersection choice (battery-tester README); expanding requires nontrivial new per-field harness work across both camdkit and opentrackio-cpp, with no specific known bug motivating it yet — lower value per unit cost than the encode/roundtrip gap above.
**Owner / revisit trigger:** revisit if a bug report or new consumer requirement names a specific field outside the current set.
**Future direct-evidence plan:** `evidence-matrix.md § EVID-005` (retired entry, reactivate if revisited).

### PROP-001 — No action scheduled: no formal shared-bug-risk checklist walkthrough

**Gap type:** evidence missing (the independence argument exists but was not stepped through `checklists/differential-independence.md` item-by-item).
**Gap disposition:** Defer.
**Owner / sign-off:** n/a.
**Revisit trigger:** if any future divergence in this harness is ambiguous about whether it reflects a real bug or a shared misreading of the spec, step through the full checklist at that point rather than relying on the summary independence argument already recorded.

**Disposition:** defer.
**Basis:** the direct independence argument already recorded (three authors/orgs/languages, no shared code) is judged sufficient for current decision-making; the full checklist walkthrough would mostly confirm what's already stated.
**Owner / revisit trigger:** see above.
**Future direct-evidence plan:** none currently planned.

### PROP-003 — No action scheduled: joint 2D pixel equivalence

**Gap type:** evidence missing.
**Gap disposition:** Defer.
**Owner / sign-off:** n/a.
**Revisit trigger:** a downstream consumer requests a joint x+y interface rather than the two independent axis theorems.

**Disposition:** defer.
**Basis:** project's own `docs/limitations.md` states this is "not planned... the x-theorem plus the p1↔p2 symmetry argument covers the content."
**Owner / revisit trigger:** see above.
**Future direct-evidence plan:** none currently planned.

### PROP-003 — No action scheduled: pure-radial case (`p1=p2=0`)

**Gap type:** evidence missing.
**Gap disposition:** Defer.
**Owner / sign-off:** n/a.
**Revisit trigger:** a real zero-tangential-distortion lens calibration is submitted for verification.

**Disposition:** defer.
**Basis:** low exposure — this effort's practical target is lenses with tracked tangential distortion; the pure-radial case is a mathematical edge case not currently motivated by a real need.
**Owner / revisit trigger:** see above.
**Future direct-evidence plan:** none currently planned.

### PROP-003 — No action scheduled: `denominatorNonzero` bound derivation

**Gap type:** evidence missing (and partly a domain question — what coefficient bounds count as "physically realistic" is not yet established by anyone).
**Gap disposition:** Defer.
**Owner / sign-off:** n/a.
**Revisit trigger:** a specific working-radius-range bound becomes necessary for a specific lens family under active verification.

**Disposition:** defer.
**Basis:** forcing a proof handoff now would hand LAPS an ill-posed target — the bound depends on a domain decision about realistic coefficient ranges that hasn't been made.
**Owner / revisit trigger:** see above.
**Future direct-evidence plan:** none currently planned.

## Handoffs

See blocks above: 1 differential-test contract (PROP-001 encode/roundtrip), 2 design-decision handoffs (PROP-004, PROP-005 — both specification reconciliations), 1 manual verification procedure (PROP-006), 5 no-action-scheduled entries (PROP-001 ×2, PROP-003 ×3). PROP-003's y-pixel gap is **not** here — it is routed to `laps-handoff.md` instead, per the Gap disposition routing table above.
