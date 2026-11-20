# LAPS Audit: adversarial-audit-p0-p1

## Audit Target

- Lean file: whole-repository scope — `opencv_opentrackio_proofs/`, `openlensio_semantics/`,
  `inverse_approximation/`, `opentrackio_parser/` (all ~73 first-party `.lean` files)
- LAPS artifact directory: `docs/laps/adversarial-audit-p0-p1/` (this audit); also
  cross-references the per-slice directories listed below
- Audit date: 2026-11-19
- Audit mode:
  - semantic audit
  - definition/model audit
  - artifact freshness audit (whole-repo build/documentation only — see note below;
    per-slice `docs/laps/*/` freshness was spot-checked, not exhaustively re-audited)
  - other: specification-fidelity audit against primary-source PDFs
    (`docs/OpenCV_to_OpenTrackIO.pdf`)

This is a cross-cutting P0/P1 adversarial audit spanning the whole repository, not a
single-theorem or single-slice review. The full theorem-by-theorem detail, the
specification traceability matrix, and the remediation backlog are written to
`audit/ADVERSARIAL_LEAN_AUDIT.md` at the repository root (the deliverable format the
task brief requested). This file is the LAPS-protocol-required companion summarizing the
same findings in the standard audit-report shape.

## Files Inspected

| File | Status | Notes |
|---|---|---|
| `lakefile.toml` | present, uncommitted modification reviewed | `defaultTargets` (line 3) excludes 59 of 63 `lean_lib` targets — see Material Findings |
| `README.md` | present | top-level claims cross-checked against Lean source; one repeated miscount found (§ below) |
| `docs/limitations.md` | present | accurate and unusually thorough; cross-checked against in-file claim-scope comments |
| `docs/specification-questions.md` | present, uncommitted modification reviewed (status-field updates only, SQ-CV-06/07) | content audited in full |
| `docs/OpenCV_to_OpenTrackIO.pdf` | present | read in full (3 pages); used for independent primary-source re-derivation, not taken on repository's word |
| `docs/OpenLensIO_v1-0-1.pdf` | present | located, not deep-read this pass (out of P0/P1 scope beyond SQ-CV-06/07 bearing) |
| `opencv_opentrackio_proofs/Pipeline/PixelIff.lean` | present | `opencv_openlensio_full_pipeline_pixel_iff` fully inspected |
| `opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean` | present | `opencv_openlensio_full_pipeline_pixel_corrected`, `physical_pixel_agreement_scale_independent_example` fully inspected |
| `opencv_opentrackio_proofs/DistortionConversion.lean` | present | paper transcription (lines 1-70) cross-checked against PDF |
| `opencv_opentrackio_proofs/MutationTests.lean` | present | theorem count verified by grep (34, not the claimed 40) |
| `opencv_opentrackio_proofs/PipelineEquivalence.lean` | present | import list checked — does not re-export `Pipeline.PixelIffCorrected` |
| `openlensio_semantics/InjectivityModel.lean` | present | full file read; `undistortPoint_injective_pure_radial` and its hypothesis-discharge chain (`radialScale_hScaleInj` etc.) fully inspected |
| `inverse_approximation/InverseApproximation.lean` | present | full file read; `D_exists_unique_preimage` and the Banach fixed-point chain fully inspected |
| `opentrackio_parser/NormalizationTheorems.lean` | present | `normalization_under_wellFormed`/`wellFormed_normalize_eq_encode` — unused-hypothesis finding |
| `opentrackio_parser/SampleEncoder.lean` | present | `encodeSample_roundtrip` signature and proof structure (exhaustive case split, not test-sampled) checked |
| `opentrackio_parser/VersionEncoder.lean` | present | `native_decide` use (line 43) identified and traced into axiom lists |
| `docs/laps/tangential-conversion-physical-fix/proof-review.md` | spot-checked, current | theorem inventory (7) matches current file content; one stale cross-reference noted (claims working-tree modifications to `PixelEquivalence.lean`/`VersionEncoder.lean` that current `git status` does not show — likely since committed; not re-verified further, out of this pass's scope) |
| `docs/laps/undistort-invertibility/proof-review.md` | spot-checked, current | slice structure (UI-00 through UI-04) matches current `InjectivityModel.lean` content |
| Remaining `docs/laps/*/` (16 other slice directories) | not individually re-audited this pass | exhaustive per-slice freshness audit is out of scope for a whole-repo P0/P1 pass; see Recommended Next Action |

## Lean Check

Commands:

```sh
lake build
# → Build completed successfully (3316 jobs), real 0m5.6s — DEFAULT TARGETS ONLY

touch opencv_opentrackio_proofs/Pipeline/PixelIff.lean
lake build
# → Build completed successfully (3316 jobs), real 0m2.8s — olean for PixelIff.lean
#   NOT regenerated (stale, confirmed via mtime comparison): staleness probe confirms
#   PipelineEquivalence is excluded from the default build graph

lake build InverseApproximation DistortionConversion PrincipalPointConversion \
  PixelEquivalence MutationTests MutationTestsY DistortionConversionCorrected \
  PipelineEquivalence RationalValueWrappers JsonRawModel DecodeError ProtocolVersion \
  VersionDecoder ProtocolDecoder RationalDecoder NonemptyArrayDecoder TimingEnumDecoders \
  TransformModel TransformDecoder CameraModel CameraDecoder LensModel LensDecoder \
  SampleModel SampleDecoder ErrorCorrectness VersionEncoder LeafEncoders TransformEncoder \
  GlobalStageEncoder TrackerEncoder PtpInfoEncoder NumericLiteralRoundtrip LeafDecoders \
  GlobalStageDecoder TrackerDecoder PtpInfoDecoder TimecodeDecoder TimecodeEncoder \
  SynchronizationDecoder SynchronizationEncoder TimingDecoder TimingEncoder CameraEncoder \
  LensSubEncoders LensEncoder SampleEncoder WellFormedSampleJson NormalizationTheorems \
  IntegrationSmoke HarnessAdapter CoordinateTypes LensSemantics SemanticBridge \
  RadialPolynomial DistortionModel DeltaSemantics ProjectionModel FovModel AngleOfView \
  ShaderCoords ExecutableSemanticOracle InjectivityModel
# → Build completed successfully (8382 jobs), real 4m30s — ALL 63 TARGETS, exit 0
```

Result: **pass**, for both the (narrow) default build and the (full) explicit-target
build. The explicit full build is what actually exercises every headline theorem named
in the task brief; the default build does not (see Material Findings, item 1).

`#print axioms` on headline declarations (`lake env lean` against a scratch file):

```
opencv_openlensio_full_pipeline_pixel_iff          → [propext, Classical.choice, Quot.sound]
opencv_openlensio_full_pipeline_pixel_corrected    → [propext, Classical.choice, Quot.sound]
physical_pixel_agreement_scale_independent_example → [propext, Classical.choice, Quot.sound]
undistortPoint_injective_pure_radial               → [propext, Classical.choice, Quot.sound]
undistortPoint_injective_zero_tangential           → [propext, Classical.choice, Quot.sound]
undistortPoint_injective_on_circle_tangential      → [propext, Classical.choice, Quot.sound]
D_exists_unique_preimage                           → [propext, Classical.choice, Quot.sound]
inverse_approx_error                               → [propext, Classical.choice, Quot.sound]
D_injective_on_disk                                → [propext, Classical.choice, Quot.sound]
encodeSample_roundtrip                             → [propext, Classical.choice, Quot.sound,
                                                        + 10 native_decide axioms (ax_1_1..ax_1_10)]
sampleNormalize_idempotent                         → same as encodeSample_roundtrip
normalization_under_wellFormed                     → same as encodeSample_roundtrip
```

Forbidden-construct scan:

```sh
grep -rEn --include="*.lean" "sorry|admit|native_decide|^unsafe|^partial" . --exclude-dir=.lake
grep -rEn --include="*.lean" "^\s*axiom\b" . --exclude-dir=.lake
```

Result: zero `sorry`/`admit`/`unsafe`/`partial`/custom-`axiom` declarations anywhere.
One genuine, disclosed-in-comment `native_decide` use (`VersionEncoder.lean:43`).

Notes:

- `propext`, `Classical.choice`, `Quot.sound` are standard Lean/Mathlib foundational
  axioms; not a defect.
- `native_decide` is a real, legitimate, narrowly-scoped trust extension (compiler/FFI
  trust, not only kernel definitional reduction) that is not currently mentioned in
  `docs/limitations.md`'s trust-model discussion — a documentation gap, not a soundness
  defect.

## Definition Inventory Check

| Definition | Intended meaning | Invariants encoded | Invariants deferred | Status |
|---|---|---|---|---|
| `RadialCoefficients` (`LensSemantics.lean`) | OTI-convention k1..k6 (numerator=odd, denominator=even) | field types only | `denominatorNonzero` deferred to a per-call-site `Prop` argument, not encoded in the type | pass — correctly deferred, consistent with spec silence on the zero-denominator case (SQ-OL-01) |
| `Coeffs` (`InverseApproximation.lean`) | A **different, generic polynomial (non-rational) 3-radial/2-tangential** coefficient vector, deliberately not the 6-coefficient rational OpenLensIO model | none (plain `ℝ` fields) | entire rational-denominator structure absent by design | pass — disclosed in-file as an intentionally independent, differently-scoped model; not conflated with `RadialCoefficients` anywhere checked |
| `WellFormedSampleJson` (`WellFormedSampleJson.lean:218`) | Schema-clean-JSON predicate | `NoDupKeys` + per-subobject well-formedness | — | **fail (see Material Findings)** — the predicate itself looks non-trivial, but it is unused in two theorems (`wellFormed_normalize_eq_encode`, `normalization_under_wellFormed`) that cite it in their names/doc-comments as load-bearing |
| `DomainPoint k` (`InjectivityModel.lean:473`) | Subtype of `SensorPoint` restricted to points where the radial denominator is nonzero, for `Function.Injective`/`Function.invFun` compatibility | carries `denominatorNonzero k (sensorRadius ε)` as a subtype proof field | none beyond that | pass |

## Theorem Inventory Check

| Item | Result |
|---|---|
| Theorem count in `MutationTests.lean` | 34 (exact, via `grep -cE "^(theorem|lemma)"`) |
| Theorem count claimed in public docs (7 locations) | 40 — **mismatch, see Material Findings** |
| Headline theorems named in task brief, located and type-inspected | 5/5 (`opencv_openlensio_full_pipeline_pixel_iff`, corrected tangential pair, `undistortPoint_injective_pure_radial`, inverse-approximation/contraction family, parser roundtrip/well-formedness family) |
| Names match source | yes |
| Classifications (U→D vs D→U, conditional vs unconditional) match in-file/doc claims | yes — the repository's own "CLAIM SCOPE" framing was independently checked against the theorem statements and found accurate |
| Final Lean check recorded after last code change | yes — both build commands above were run against the current working-tree state (including the uncommitted `lakefile.toml`/`docs/specification-questions.md` edits, which were reviewed as part of this audit, not reverted first) |

## Semantic Audit Summary

| Check | Result | Notes |
|---|---|---|
| Statement laundering | pass | no case found of a theorem proving a proxy property while claiming the full-strength one |
| Definition-model mismatch | pass, with one flagged exception | `WellFormedSampleJson` unused-hypothesis case (below) is a statement-framing issue, not a type-level model mismatch |
| Comment/formal mismatch | **fail** | `README.md:92-93` and `NormalizationTheorems.lean:60` frame well-formedness as load-bearing when the Lean proof shows it is unused |
| Vacuity | pass | no impossible-hypothesis or trivially-true headline theorem found |
| Weakened claims | pass | iff-shaped theorems are genuinely bidirectional; injectivity theorems are genuinely global where claimed global |
| Proxy properties | pass | — |
| Over-strong/circular hypotheses | pass | `hScaleInj`, `hDet`, `hcontract` all independently classified as logically-prior, non-circular, and (where applicable) constructively dischargeable |
| Automation hiding hard step | pass | proofs use `ring`/`field_simp`/`nlinarith`/explicit `HasDerivAt` calculus appropriately for their goal shapes; no unexplained `aesop`/`grind` closing a nontrivial goal was found in the files read |
| Runtime failure replacing proof | pass | no `partial`/`panic`/unchecked-indexing found |
| Forbidden constructs | pass | zero `sorry`/`admit`/custom `axiom`/`unsafe`; one disclosed, narrowly-scoped `native_decide` |
| Build/artifact inclusion | **fail** | `defaultTargets` excludes the files containing every headline theorem named in the task brief |

## Material Findings

| Severity | Finding | Required Action |
|---|---|---|
| high | `lakefile.toml:3` `defaultTargets` includes only 4 of 63 `lean_lib` targets; plain `lake build` (the command `README.md:199-208` documents) never type-checks `Pipeline/*` (so `opencv_openlensio_full_pipeline_pixel_iff` is unchecked by the documented command), `openlensio_semantics/*` (so `undistortPoint_injective_pure_radial` is unchecked), `inverse_approximation/*`, or the parser's encoders/`NormalizationTheorems.lean` (so `encodeSample_roundtrip`/`sampleNormalize_idempotent` are unchecked). Confirmed by a staleness probe (touched `PixelIff.lean`, re-ran `lake build`, olean timestamp did not update) and by import-closure computation (28 files reached vs. ~73 total). Confirmed NOT a proof defect: explicit full build (`lake build <all 63 targets>`) succeeds, 8382 jobs, exit 0. | Add the 59 missing targets to `defaultTargets`; update README's expected job count; verify whether CI (if any) already passes explicit targets |
| medium | "40 mutation-test theorems" cited as anti-vacuity evidence in 7 documents (`README.md:57`, `docs/specification-questions.md:157`, 5 files under `docs/maps/`); actual count in `MutationTests.lean` is 34 (verified by exact grep, full name list cross-checked) | Correct the count in all 7 locations, or add 6 more theorems to reach 40 |
| medium | `wellFormed_normalize_eq_encode` and `normalization_under_wellFormed` (`NormalizationTheorems.lean:55-64`) take `WellFormedSampleJson j` as a named-but-unused (`_`-bound) hypothesis; both theorems are provably true from `decodeSample j = .ok s` alone, contradicting the load-bearing framing in `README.md:92-93` and the in-file comment at line 60 | Remove the unused hypothesis and restate both theorems in terms of `decodeSample j = .ok s` alone, or document why it is retained despite being redundant |
| low | `native_decide` (`VersionEncoder.lean:43`) propagates 10 extra compiler/FFI-trust axioms into `encodeSample_roundtrip`, `sampleNormalize_idempotent`, `normalization_under_wellFormed`; legitimate and disclosed in a local comment, but not mentioned in `docs/limitations.md`'s trust-model discussion | Add one sentence to `docs/limitations.md`'s parser section |
| low | `PipelineEquivalence.lean`'s "compatibility re-export" does not import `Pipeline.PixelIffCorrected`, so `import PipelineEquivalence` alone does not bring the corrected-tangential theorem into scope | Add the missing import, or document the gap in the file's own header comment |
| low | `README.md:43`'s one-sentence headline summary of the pipeline iff omits the `hp : p1≠0∨p2≠0` caveat that is present in the linked "Claim scope" paragraph and in `docs/limitations.md` | Inline the caveat alongside the headline sentence |

Independently-confirmed, open specification question (not a repository defect — reported
here because it was substantially strengthened by this audit's own primary-source
re-derivation, not merely repeated from the repository's self-report):

> Direct substitution into the primary source PDF's own stated coordinate relation
> `ε'_{x,d} = F·x''` (`docs/OpenCV_to_OpenTrackIO.pdf`, p.2) shows that the paper's own
> worked tangential-distortion derivation (`q1=p1/F²`, p.3) is dimensionally inconsistent
> with that relation once `x''` is correctly decomposed into its multiplicative-radial and
> additive-tangential parts; `q1=p1/F` is what the relation requires. This independently
> corroborates SQ-CV-06 from a fresh reading of the primary source, not from trusting the
> repository's restatement of its own claim. Full derivation in
> `audit/ADVERSARIAL_LEAN_AUDIT.md` §4.1. Status remains open pending maintainer response
> (outreach sent 2026-08-15, per `docs/specification-questions.md`).

## Notes

| Note | Suggested Cleanup |
|---|---|
| `docs/laps/tangential-conversion-physical-fix/proof-review.md:94` references working-tree modifications to `PixelEquivalence.lean`/`VersionEncoder.lean` that current `git status` does not show (likely since committed) | Low priority; not re-verified beyond noting the discrepancy, out of scope for this pass |
| 16 of 18 `docs/laps/*/` slice directories were not individually freshness-audited in this pass (only `tangential-conversion-physical-fix` and `undistort-invertibility` were spot-checked and found current) | A dedicated `/laps-audit` pass per remaining slice would close this gap; not required to validate the P0/P1 findings reported here, which were independently re-derived from the Lean source and primary-source PDF rather than from the slice artifacts |
| "~100 public theorems" aggregate claim (`docs/opentrackio-proof-summary.md:7`) was not independently re-verified against a precise public/private census; a blunt whole-repo grep returns 185 but is not a like-for-like comparison (includes private helpers and uncommitted in-progress files) | Flagged as unverified, not as a confirmed discrepancy, in `audit/ADVERSARIAL_LEAN_AUDIT.md` §8 |

## Artifact Status

- Proof capsule current: not checked (whole-repo pass; no single proof-capsule applies)
- Statement audit current: not checked (whole-repo pass)
- Proof plan current: not checked (whole-repo pass)
- Proof run log current: n/a — no Lean code was edited by this audit
- Proof review current: spot-checked for 2/18 slices (see Files Inspected); current for both checked
- Work queue current, if applicable: not checked
- First-slice contract current, if applicable: n/a
- Ambiguity register current, if applicable: not checked
- Algebra plan current, if applicable: n/a
- Final Lean command recorded after last code change: yes
- Artifact theorem count matches Lean file: **no** — see Material Findings (34 vs. claimed 40)
- Artifact theorem names match Lean file: yes, for all headline theorems inspected
- Artifact classifications match across files: yes, for all headline theorems inspected
- Load-bearing definitions match documented intent: **no** for `WellFormedSampleJson` as cited in the two affected theorems (see Material Findings); yes for all other definitions inspected

## Verdict

**repair recommended**

The underlying mathematics is sound — every headline theorem compiles, depends only on
standard axioms (plus one disclosed `native_decide` use), and is not vacuous, circular,
or statement-laundered. This is not `rejected`: no blocker-level defect (no `sorry`, no
unsound construct, no proof that fails to compile, no theorem that doesn't mean what it
claims to mean) was found. But it is not `accepted` or `accepted with notes` either: the
build-configuration gap (item 1) means the documented verification procedure does not
actually verify the headline claims, which is exactly the kind of issue this audit
protocol treats as blocking full acceptance until repaired, and the repeated
documentation miscount (item 2) and unused-hypothesis framing (item 3) are independently
verifiable, concrete defects a careful reviewer should not have to re-discover.

## Recommended Next Action

Fix `lakefile.toml:3`'s `defaultTargets` to cover all 63 `lean_lib` targets (or restructure
with exhaustive `globs`) and re-run `lake build` with no explicit target list to confirm
the documented command now reaches every headline theorem; correct the "40 mutation-test
theorems" count in all 7 citing documents; and resolve the unused `WellFormedSampleJson`
hypothesis in `NormalizationTheorems.lean:55-64`. These three items are independently
small, mechanical fixes — none requires re-deriving any mathematics — and together they
would move this repository from `repair recommended` to `accepted with notes` on a
follow-up audit. Full detail, line-level citations, and the primary-source dimensional
analysis are in `audit/ADVERSARIAL_LEAN_AUDIT.md`.
