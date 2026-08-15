# Proof Review — Tangential Conversion Physical-Semantics Fix

## Review target

- Theorem / task slug: tangential-conversion-physical-fix
- File: `opencv_opentrackio_proofs/DistortionConversionCorrected.lean`,
  `opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean`
- Theorem name: 7 theorems (full inventory below)
- Reviewed command: `/laps-start` (implementation authorized in the initial task)

## Review evidence

- Repo path / identifier: `opentrackio-proof` (local working tree)
- Repo commit: `8c9add555337df0f6e67c874d475ec3eee78d543` (HEAD at review time; working tree has uncommitted new files — this commit is the base the changes sit on, not a claim that the changes are committed)
- LAPS version: skill bundle as installed at `~/.claude/commands/laps/laps`
- Review date: 2026-08-15
- Review scope: two new files (module-level)
- Acceptance claim level: module (`DistortionConversionCorrected`, and `PixelIffCorrected` within the existing `PipelineEquivalence` module)
- Review type: exhaustive theorem audit (of the two new files only — this review does not re-audit any existing file)
- Strongest required Lean command: `lake build DistortionConversionCorrected` and `lake build PipelineEquivalence` (module-level, since acceptance is claimed at module level, not whole-repo)
- Strongest required Lean command run: yes
- Final Lean command: `lake env lean opencv_opentrackio_proofs/DistortionConversionCorrected.lean` (exit 0, no warnings); `lake env lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean` (exit 0, 1 warning); `lake build DistortionConversionCorrected` (`Build completed successfully (3287 jobs)`); `lake build PipelineEquivalence` (`Build completed successfully (3299 jobs)`)
- Final Lean result: pass (both files, both build targets)
- Warnings: one, `unused variable hF_pos` in `PixelIffCorrected.lean:45`; matches a pre-existing pattern already present in the unmodified `PixelSufficiency.lean` (same hypothesis, same unused status) — not a new defect, see AMB-TCF-002
- Search / grep command(s): `grep -REn --include="*.lean" "sorry|admit|set_option warn\.sorry|^unsafe|^partial|^axiom" opencv_opentrackio_proofs/DistortionConversionCorrected.lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean`
- Search / grep result(s): no matches (exit 1)
- Search command executability: all executable
- Lean files reviewed: 2 (both new; no existing file re-reviewed as part of this task, per non-negotiable rule 1/2 — they were read but not edited)
- Theorem declarations reviewed: 7 — exact inventory via `grep -n "^theorem "`:
  1. `tangential_q1_conversion_physical` (`DistortionConversionCorrected.lean:42`)
  2. `tangential_q2_conversion_physical` (`DistortionConversionCorrected.lean:60`)
  3. `whole_tangential_field_iff_physical` (`DistortionConversionCorrected.lean:83`)
  4. `whole_tangential_field_2d_iff_physical` (`DistortionConversionCorrected.lean:115`)
  5. `all_distortion_conversions_iff_physical` (`DistortionConversionCorrected.lean:147`)
  6. `opencv_openlensio_full_pipeline_pixel_corrected` (`Pipeline/PixelIffCorrected.lean:41`)
  7. `physical_pixel_agreement_scale_independent_example` (`Pipeline/PixelIffCorrected.lean:119`)
- Inventory count type: exact
- Inventory command or method: `grep -n "^theorem " opencv_opentrackio_proofs/DistortionConversionCorrected.lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean`
- Theorem inventory attached: yes (above)
- Exhaustive claim allowed: yes (exact inventory produced, matches file contents at review time)
- Placeholder hygiene evidence: grep above, clean
- Diagnostics evidence: see `proof-run-log.md` diagnostics checks (both pass)
- Artifact freshness status: current — all Lean commands above run after the final code edit in this session
- metrics.md required: yes (algebra-heavy, multi-theorem-family task)
- metrics.md finalized: yes (see `metrics.md`)
- Evidence gaps: none for the module-level claim made here. Note: no whole-repo `lake build` was run (not claimed — acceptance claim is module-level only, per the "strongest required Lean command" for this scope)

## Classification consistency check

- Final Lean result known: yes
- Warnings known: yes
- Strongest required Lean command run for claimed scope: yes
- `lake build` run if claiming whole-repo acceptance: n/a (no whole-repo claim made)
- Search commands executable: yes
- Theorem inventory exact if claiming exhaustive: yes
- Metrics status recorded if required: yes
- Verdict/evidence consistent: yes
- Required Action split present: yes (below)
- Verification/build action non-none if build evidence incomplete: n/a (evidence complete)
- Process evidence action non-none if process evidence incomplete: n/a (evidence complete)

## Theorem statements

See `proof-capsule.md` for the full specification-level texts; final compiled
texts match those exactly except where field types differ trivially
(none — all match verbatim). No statement drifted from the capsule during
implementation, except the one authorized shape decision (AMB-TCF-001,
recorded pre-implementation).

## Verification command

```sh
lake env lean opencv_opentrackio_proofs/DistortionConversionCorrected.lean
lake env lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean
lake build DistortionConversionCorrected
lake build PipelineEquivalence
```

All four: pass.

## Kernel status

- File compiles: yes (both)
- Full build passes (module-level, as required for this claim): yes
- No `sorry`: yes
- No `admit`: yes
- No unauthorized `axiom`: yes
- No unauthorized `constant`: yes
- No `unsafe`: yes
- No `partial`: yes
- No `set_option warn.sorry false`: yes
- No sorry replaced with axiom or constant: yes
- No runtime failure replacing proof obligations: yes
- No forbidden theorem-statement changes: yes — zero edits by this task to any existing file. `DistortionConversion.lean`, `Pipeline/PixelIffHelpers.lean`, `Pipeline/PixelSufficiency.lean`, `Pipeline/PixelIff.lean` are all untouched, confirmed via `git diff` showing this task's only changes are the two new files plus a scoped `lakefile.toml` addition (`git diff lakefile.toml` shows exactly one new `[[lean_lib]]` block, nothing else). Note: `git status` also shows `opencv_opentrackio_proofs/PixelEquivalence.lean` and `opentrackio_parser/VersionEncoder.lean` as modified in the working tree — these are **pre-existing uncommitted changes from before this session** (unrelated doc-comment and native_decide-trust-note edits, confirmed by their content having nothing to do with this task), not edits made by this task.
- No unauthorized definition changes: yes (no definitions changed anywhere; these are all `theorem`s over raw `ℝ`, no new definitions introduced)
- No unauthorized import changes: yes — one new `[[lean_lib]]` entry in `lakefile.toml` for `DistortionConversionCorrected` (authorized in capsule); `PixelIffCorrected.lean` needed no lakefile change (covered by existing `Pipeline.+` glob)
- No unauthorized global `[simp]`, `[grind]`, or `grind_pattern` changes: yes (none used)

## Placeholder hygiene check

- All `sorry`s removed or explicitly authorized as non-final scaffold: yes (none present)
- No `set_option warn.sorry false` in any touched file: yes
- No `sorry` replaced with `axiom` or `constant`: yes
- If temporary scaffolding is authorized: n/a
- Slice marked incomplete if any authorized `sorry` remains: n/a

## Diagnostics check

```
DIAGNOSTICS CHECK:
- Narrow Lean command run: lake env lean on both new files
- Result: pass (both)
- Warnings present: yes — 1 (unused hF_pos, PixelIffCorrected.lean, expected/parity)
- Sorry warnings present: no
- `set_option warn.sorry false` in any file: no
- Linter warnings present: yes — the one noted above
- Unexpected generated files: no
- UTF-8 BOM or encoding problems: no
```

## Statement audit

Plain-English theorem (main result,
`opencv_openlensio_full_pipeline_pixel_corrected`):

> If all radial coefficient conversions hold (unchanged from the paper) and
> the tangential coefficients convert by the physically-corrected formula
> q1 = p1/F, q2 = p2/F (rather than the paper's stated p/F²), and the usual
> focal-length and principal-point relations hold, then the OpenCV and
> OpenLensIO pixel-x outputs agree for every normalised input point —
> unconditionally, with no further requirement on the sensor-scale ratio
> ws/w matching fx.

Original human intent (from the task):

> Determine whether the corrected pipeline theorem's residual condition
> collapses to something trivially true (full pixel agreement) rather than
> ws/w = fx.

Does this match the original intent? **yes**. The theorem directly answers
the question asked: it proves unconditional pixel agreement (the "trivially
true" outcome), and the companion `physical_pixel_agreement_scale_independent_example`
theorem mechanically confirms the naive `ws/w = fx` requirement genuinely
does not survive (by exhibiting a case where it fails yet pixel agreement
still holds), rather than merely asserting this in prose.

## Parameter and hypothesis audit

| Name | Type / Role | Used? | Necessary? | Suspicious? | Notes |
|---|---|---:|---:|---:|---|
| `hF : F ≠ 0` | division guard | yes | yes | no | needed for `hq1`,`hq2`,`hl*` divisions and `hF_eq` |
| `hF_pos : 0 < F` | sign guard | no (Lean-confirmed via warning) | no | no | kept for signature parity with `opencv_openlensio_full_pipeline_pixel_iff`/`_sufficiency`, both of which also don't use it — pre-existing pattern, not a new vacuity risk (see AMB-TCF-002); not a "suspicious" hypothesis since dropping it would only be a cosmetic signature change, not a proof-strength change |
| `hw : w ≠ 0`, `hws : ws ≠ 0` | division guards | yes | yes | no | used in `hfx` derivation and final `field_simp` |
| `hl1..hl6` | radial conversion | yes | yes | no | unchanged from baseline, used in `h_num`/`h_den` |
| `hq1 : q1 = p1/F`, `hq2 : q2 = p2/F` | **corrected** tangential conversion | yes | yes | no | the load-bearing change; used directly in the final `rw` |
| `hF_eq`, `hΔPx` | pinhole geometry relations | yes | yes | no | unchanged from baseline |
| `hden` | denominator regularity | yes | yes | no | unchanged from baseline |
| `hp : p1 ≠ 0 ∨ p2 ≠ 0` (baseline only) | — | n/a — **absent from corrected theorem** | n/a | no | correctly dropped: it existed only to support the baseline's → direction extraction of `ws/w=fx`, which no longer exists here (see statement-audit.md) |
| `hscale : ws/w = fx` (baseline only) | — | n/a — **absent from corrected theorem** | n/a | no | correctly dropped: no longer a precondition, per the whole point of this investigation |

No hypothesis in the 7 new theorems is unused except `hF_pos` (explained
above, matches baseline pattern, kept for parity not accidentally).

## Conclusion audit

- Conclusion is strong enough: yes — `opencv_openlensio_full_pipeline_pixel_corrected`'s
  conclusion is *stronger* than the baseline's (unconditional equality vs. an
  iff requiring an extra hypothesis-satisfying condition)
- Conclusion is not weakened: yes — confirmed strengthened, not weakened
- Conclusion is not a proxy property: yes — it is exactly the pixel-agreement
  statement asked about, same shape as the baseline minus the now-unnecessary
  extra condition
- Conclusion is not merely test-shaped or bounded without justification: yes
- Conclusion expresses semantic property rather than implementation artifact: yes

Notes: the shape change (iff → plain equality) is the one authorized,
load-bearing decision in this task (AMB-TCF-001) — reviewed and confirmed
correct: attempting to keep the iff shape would require proving a false
statement, and `physical_pixel_agreement_scale_independent_example` is the
kernel-checked evidence for that falsity claim, not just an assertion.

## Proof strategy

First meaningful tactic (per theorem): witness instantiation (`hconsist 1 1`,
`h 0 1`/`h 1 0`/`h 1 1`) for Layer 1/2, followed by algebra closure; `rw`
chain + `field_simp`/`ring` for the pipeline-level theorem.

Expected proof shape: algebraic normalization (field_simp/ring/linear_combination)
+ one delegated-theorem cancellation step (`mul_right_cancel₀`) per F-power
reduction.

Does the strategy match the theorem shape? yes — these are pure real-algebra
identities/implications; the strategy used throughout the codebase for this
theorem family (witness specialization + field_simp/ring/nlinarith) is
appropriate here, with one genuinely new ingredient (`mul_right_cancel₀`)
required because canceling a single F is not a `ring`-level fact.

## Hard-step identification

The proof works because of:

- algebra solver (`linear_combination`, `field_simp`, `ring`)
- delegated theorem (`mul_right_cancel₀` for one-F-power cancellation;
  `right_ne_zero_of_mul` for deriving `fx ≠ 0` without `hscale`)

Key step (Layer 1, representative of the genuinely new ingredient in this
task versus the baseline file):

```lean
have hcancel : p1 * F = (q1 * F) * F := by linear_combination h11
have hp1eq : p1 = q1 * F := mul_right_cancel₀ hF hcancel
```

Why this step works: `h11 : F*p1 = q1*F*F` is a ring rearrangement away from
`p1*F = (q1*F)*F` (no cancellation involved — `linear_combination` handles
this). The genuine cancellation of one F factor is then isolated into
`mul_right_cancel₀ hF`, which is the only place `hF : F ≠ 0` does real work
beyond enabling division notation. This is the "hard step" the proof plan
anticipated (F-cancellation is not a ring fact) and it was correctly
identified and isolated rather than papered over with a broader tactic.

Key step (pipeline-level, the theorem that actually answers the user's
question):

```lean
rw [h_num, h_den, hq1, hq2, hΔPx, hF_eq]
field_simp [hw, hws, hfx, hden_xy]
ring
```

Why this step works: after substituting the corrected `q1=p1/F, q2=p2/F` and
`F=(w/ws)*fx`, both sides become the same rational function of
`k1..k6, p1, p2, fx, cx, w, ws, x', y'` — `field_simp` clears all denominators
(using the four nonzero facts) and `ring` confirms syntactic equality of the
resulting polynomials. This automation is goal-shaped (not opaque): the
`have`s immediately preceding it (`h_num`, `h_den`, `hfx`) supply exactly the
facts `field_simp`/`ring` need, and no broader `simp`/`aesop` search was used.

## Automation review

Automation used: `field_simp`, `ring`, `linear_combination`, `nlinarith` (Layer 2, only in the pre-existing baseline-mirrored step, not new), `norm_num` (counterexample witness).

| Tactic | Goal shape | Explicit facts supplied | Result | Hard step explained? |
|---|---|---|---|---:|
| `linear_combination h11` (and analogous) | ring rearrangement of a hypothesis, no cancellation | `h11` | closed sub-`have` | yes |
| `mul_right_cancel₀ hF hcancel` | one-F cancellation | `hF`, `hcancel` | closed | yes |
| `field_simp [hF2,hF4,hF6]` | clear denominators in radial `h_num`/`h_den` | nonzero powers of F | closed | yes (mirrors baseline exactly) |
| `field_simp [hw,hws,hfx,hden_xy]; ring` | final pixel-equality closure | all four nonzero facts | closed | yes |
| `norm_num` (counterexample) | numeric equality/inequality checks on concrete rationals | none needed | closed | yes (trivial arithmetic) |

Automation verdict: goal-shaped and appropriate throughout. No instance of
automation hiding a hard step — every nontrivial closure is preceded by an
explicit `have` supplying exactly the facts needed, following this
codebase's existing style.

## Helper lemma review

| Helper | Local or global? | Purpose | Necessary? | Statement audited? | Notes |
|---|---|---|---:|---:|---|
| (none added) | — | — | — | — | The proof plan anticipated needing a local `tangential_scaled_eq_physical` helper; it was not needed — `field_simp`/`ring` handled the substituted expression directly in one pass. Recorded as a plan deviation in `proof-run-log.md`, not a silent omission. |

## Import and annotation review

| Change | Authorized? | Justification | Risk |
|---|---:|---|---|
| `import DistortionConversion` in both new files | yes | matches capsule; same import baseline files use | none |
| `[[lean_lib]] name = "DistortionConversionCorrected"` in `lakefile.toml` | yes | new top-level file needs its own lib entry, per existing per-file pattern in this directory | none |
| No lakefile change for `PixelIffCorrected.lean` | yes | already covered by `PipelineEquivalence`'s `Pipeline.+` glob | none |

No `[simp]`, `[grind]`, or `grind_pattern` annotations used.

## Anti-pattern scan

| Anti-pattern | Found? | Evidence | Severity |
|---|---:|---|---|
| Statement laundering | no | | |
| Vacuous theorem | no | hypothesis audit above shows no self-implying hypothesis | |
| Weakened conclusion | no | conclusion is strengthened relative to baseline, not weakened | |
| Over-strong hypotheses | no | fewer hypotheses than baseline (`hp`, `hscale` dropped, both correctly) | |
| Unused hypotheses | yes (1) | `hF_pos` in `PixelIffCorrected.lean` | low — matches pre-existing baseline pattern, kept for signature parity, not silently smuggled in |
| Tactic soup | no | each proof is a short, structured sequence with named `have`s | |
| Automation hiding hard step | no | see hard-step section | |
| Algebra rewrite ping-pong | no | | |
| Misused `<;>` | no | `<;>` not used in the final proofs (removed from an earlier draft that used it opaquely; final proofs use explicit sequential tactics) | |
| Arbitrary case split | no | | |
| Runtime failure replacing proof | no | | |
| Fuel weakening total correctness | n/a | no recursion/fuel in this task | |
| Test-overfitting | no | the counterexample theorem uses one concrete witness by design (existential statement), not a stand-in for a universal claim | |
| Specification unreadable or misaligned | no | statement-audit.md confirms alignment | |
| Manual simulation of available automation | no | `ring`/`field_simp`/`linear_combination` used instead of manual `rw` chains | |
| Annotation desperation | no | no annotations added | |
| Opaque automation success | no | every automation call is preceded by explicit supporting `have`s | |
| Verifier confusion | no | | |

## Required action

### Semantic proof action

- none

### Verification/build action

- none (both narrow and module-level checks already run, fresh, post-final-edit)

### Process evidence action

- none

## Rejection criteria check

- theorem statement does not match intended claim: false
- theorem is vacuous: false
- conclusion was weakened without authorization: false
- proof relies on impossible or unjustified hypotheses: false
- proof proves a proxy property while claiming the intended property: false
- forbidden constructs remain: false
- runtime failure replaces proof obligations: false
- automation hides the hard step and no explanation can be recovered: false
- proof does not compile under the relevant Lean command: false

None triggered.

## Artifact freshness check

| Artifact | Status | Notes |
|---|---|---|
| `proof-capsule.md` | current | matches final theorem texts |
| `statement-audit.md` | current | AMB-TCF-001 decision confirmed by the compiled proof |
| `proof-plan.md` | current | one deviation noted (no helper lemma needed), recorded in run log |
| `proof-run-log.md` | current | updated after final Lean commands |
| `subgoal-ledger.md` | n/a | not used — task small enough for inline attempts/failures in run log |
| `work-queue.md` | n/a | single-slice medium task |
| `first-slice-contract.md` | n/a | single-slice medium task |
| `algebra-plan.md` | n/a | no `ALGEBRA STOP` triggered (within two-failure tripwire budget) |
| `port-audit.md` | n/a | not a source-code port task |
| `handoff.md` | n/a | single session, no handoff needed |

Lean check timing:

- Final Lean command: `lake env lean` on both files, then `lake build DistortionConversionCorrected` and `lake build PipelineEquivalence`
- Run after last code change: yes
- Theorem count in Lean file: 7
- Theorem count in this review: 7
- All theorems in this review covered by proof-run-log.md: yes

## Metrics finalization

- metrics.md required: yes
- metrics.md updated after final Lean command: yes
- final score recorded: yes
- semantic concerns reflected in metrics: yes (none found)
- artifact freshness reflected in metrics: yes

## Final verdict

**accepted**

## Final notes

- The task's central question — "does the residual condition collapse to
  trivially true?" — is answered **yes**, with two independent pieces of
  kernel-checked evidence: (1) the corrected pipeline theorem proves
  unconditional pixel agreement, and (2) the counterexample theorem exhibits
  `ws/w ≠ fx` with pixel agreement still holding, directly refuting the naive
  ported iff.
- No existing theorem, definition, or file was modified by this task.
  `git diff` confirms this task's changes are exactly the two new files plus
  a scoped `lakefile.toml` addition. (Two unrelated files —
  `PixelEquivalence.lean`, `VersionEncoder.lean` — show as modified in
  `git status`; these are pre-existing uncommitted changes from before this
  session and are out of scope for this task.)
- This review does not re-certify any existing theorem in
  `DistortionConversion.lean` or `Pipeline/*.lean` — those are out of scope
  and were read-only throughout.
