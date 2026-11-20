# Adversarial Lean 4 Proof Audit — P0/P1

**Scope:** pipeline conversion theorems (`opencv_opentrackio_proofs/`), OpenLensIO semantics
(`openlensio_semantics/`), inverse approximation (`inverse_approximation/`), and the
OpenTrackIO parser (`opentrackio_parser/`). P0/P1 severity only; cosmetic issues out of
scope for this pass.

**Auditor posture:** adversarial. Every headline theorem is treated as potentially
overstated until its exact Lean type, dependency graph, and build inclusion are
independently inspected. Repository claims (including the repository's own "suspected
paper error" claim) are independently re-derived, not taken on trust.

**Repository state audited:**
- Commit: `0c065db` ("added research into kalibr lens data to see if we can use for testing"), branch `main`, up to date with `origin/main`.
- Working tree at audit time: `docs/specification-questions.md` and `lakefile.toml` modified but uncommitted (both reviewed below); untracked `docs/laps/y-pixel-equivalence/`, `docs/maps/`, `opencv_opentrackio_proofs/MutationTestsY.lean`, `opencv_opentrackio_proofs/Pipeline/PixelIffHelpersY.lean`, `Pipeline/PixelIffY.lean`, `Pipeline/PixelSufficiencyY.lean` (y-axis work in progress — not part of the committed, documented, or default-built surface; not treated as part of the audited claims).
- Lean toolchain: `leanprover/lean4:v4.29.0` (`lean-toolchain`).
- Mathlib: pinned at `rev = "v4.29.0"` in `lakefile.toml`'s `[[require]]`; `lake-manifest.json` resolves this to commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. Dependency revisions recorded: `aesop 7152850`, `batteries 756e332`, `Qq 707efb5`, `proofwidgets 3c52dee`, `importGraph 48d5698`, `Cli 7802da0`.

---

## 1. Executive verdict

**The mathematics is sound; the build configuration and the public documentation are
not.** Every headline theorem named in the task brief — `opencv_openlensio_full_pipeline_pixel_iff`,
the corrected-tangential theorem, `undistortPoint_injective_pure_radial`, the inverse-existence
theorem, and the parser roundtrip/normalization theorems — compiles and depends on only
the three standard Lean/Mathlib foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`), with one narrow, disclosed exception (`native_decide` in the parser's
version-digit roundtrip, §2.4). No `sorry`, `admit`, hidden `axiom`, or `unsafe`/`partial`
declarations exist anywhere in the ~73 first-party `.lean` files. The repository's internal
scope-limiting documentation (`docs/limitations.md`, `docs/specification-questions.md`,
and extensive in-file "CLAIM SCOPE" comments) is unusually honest and mostly accurate —
this is not a typical case of theorem-statement overclaiming.

However, three findings are serious enough to block treating this repository's README/
summary claims as fully verified as written:

1. **(P0 — build configuration)** `lakefile.toml`'s `defaultTargets` list excludes
   essentially every headline theorem from the documented `lake build` command. A fresh
   clone following the README's own build instructions type-checks only 28 of the
   repository's ~73 Lean files — none of `Pipeline/*` (so `opencv_openlensio_full_pipeline_pixel_iff`
   itself is never checked by the documented command), none of `openlensio_semantics/`
   (so `undistortPoint_injective_pure_radial` is never checked), none of
   `inverse_approximation/`, and none of the parser's encoders or normalization theorems
   (so `encodeSample_roundtrip` and `sampleNormalize_idempotent` are never checked). This
   is a reproducibility/trust-chain defect, not a proof defect: building every target
   explicitly (`lake build <all 63 lean_lib names>`) succeeds cleanly (8382 jobs, exit 0,
   only linter-level warnings). See §2.1–§2.3.

2. **(P1 — documentation overclaim, repeated)** "40 mutation-test theorems" is asserted
   as load-bearing anti-vacuity evidence in **seven** separate documents (`README.md`,
   `docs/specification-questions.md`, and five files under `docs/maps/`). The actual count
   in `opencv_opentrackio_proofs/MutationTests.lean` is **34**. See §5.1.

3. **(P1 — confirmed internal inconsistency in the published derivation, precisely
   scoped)** A hostile-review pass (§4.1) reconstructed both formulas from scratch against
   *both* primary sources (`docs/OpenCV_to_OpenTrackIO.pdf` and, newly for this pass,
   the authoritative base spec `docs/OpenLensIO_v1-0-1.pdf`), deliberately trying to find a
   reading under which the published `q=p/F²` is correct. None was found. Two independent
   derivation methods (direct substitution into the paper's own stated coordinate identity,
   and function conjugation under coordinate scaling) and two hand-verifiable numeric
   counterexamples all show the same result: `q=p/F` is what the paper's own
   `ε'_{x,d}=F·x''` coordinate relation requires; `q=p/F²` produces pixel outputs
   inconsistent with OpenCV's forward model whenever `F≠1` and tangential distortion is
   nonzero. **This is reported as three distinct, non-conflatable claims** (§4.1.5): (i) an
   established mathematical fact about the stated coordinate model, independent of either
   document's authority; (ii) a demonstrated internal inconsistency in the conversion
   paper's own tangential derivation relative to its own radial derivation and its own
   stated coordinate identity — not a claim that OpenLensIO's native distortion model or
   the OpenTrackIO standard as a whole is defective; and (iii) matters that remain
   genuinely unresolved — the authors' possible undocumented intent, which (if either)
   formula any real implementation uses (checked directly against two reference
   implementations: **neither implements this conversion at all**), and, separately and
   explicitly *not* resolved by this finding, how either coefficient convention relates to
   OpenLensIO's *native* D→U undistortion model (SQ-CV-07 — same-direction coordinate
   conjugacy and native inverse-model interoperability are different mathematical
   obligations; see §4.1.5). See §4.1 and §5.2. Open pending the maintainers' response
   (sent 2026-08-15, per `docs/specification-questions.md` SQ-CV-06/07).

Two further P1-adjacent findings concern the parser:

4. A pattern of **vacuous hypotheses** in `NormalizationTheorems.lean`: both
   `wellFormed_normalize_eq_encode` and `normalization_under_wellFormed` take
   `WellFormedSampleJson j` as a named hypothesis (bound as `_`, confirming it is unused)
   that plays no role in either proof. The theorems are true unconditionally whenever
   `decodeSample j = .ok s` holds, contradicting the README's framing ("normalization
   preserves decoded semantics for well-formed inputs"). See §3.5.

5. `native_decide` (not `decide`) is used once, in `VersionEncoder.lean:43`, and this
   propagates ten additional `Lean.ofReduceBool`-style compiler-trust axioms into every
   theorem that transitively depends on `encodeVersionDigit_roundtrip` — including
   `encodeSample_roundtrip`, `sampleNormalize_idempotent`, and
   `normalization_under_wellFormed`. This is a legitimate, disclosed-in-comment use, but
   it is not mentioned in `docs/limitations.md`'s trust-model discussion, and the three
   affected theorems are not pure-kernel results in the way the pipeline/semantics
   theorems are. See §2.4.

None of these findings invalidate the underlying mathematics. They are, respectively: a
Lake configuration bug, a documentation-accuracy bug (repeated seven times), an
independently-strengthened open specification question, a statement-framing bug, and an
undocumented (but not unsound) trust-model footnote.

---

## 2. Reproducibility and trust audit

### 2.1 Build: documented command vs. actual coverage

`lakefile.toml:3`:

```toml
defaultTargets = ["DistortionConversion", "PrincipalPointConversion", "PixelEquivalence", "HarnessAdapter"]
```

Only 4 of the 63 `[[lean_lib]]` targets declared in `lakefile.toml` are in this list.
`README.md:199-208` documents the build procedure as:

```sh
lake update
lake build
```

> Expected: `Build completed successfully (N jobs).` where N is in the low thousands.

**Empirical test 1 (staleness probe).** `opencv_opentrackio_proofs/Pipeline/PixelIff.lean`
(home of `opencv_openlensio_full_pipeline_pixel_iff`) was `touch`ed, then `lake build`
(no args) was run. Source mtime became `Nov 19 16:26:39 2026`; the corresponding
`.lake/build/lib/lean/Pipeline/PixelIff.olean` remained at `Aug 15 18:02:05 2026` —
unchanged. Job count and wall time were identical to the prior run (`3316 jobs`, ~3-6s).
Plain `lake build` did not even notice the file was stale, because `Pipeline/PixelIff.lean`
belongs to the `PipelineEquivalence` library target, which is not in `defaultTargets`.

**Empirical test 2 (closure computation).** Computing the transitive `import` closure of
each of the four default targets' root modules gives:

| Default target | Root file | Transitive closure (files) |
|---|---|---|
| `DistortionConversion` | `opencv_opentrackio_proofs/DistortionConversion.lean` | 1 (itself; imports only `Mathlib.Tactic`) |
| `PrincipalPointConversion` | `opencv_opentrackio_proofs/PrincipalPointConversion.lean` | 1 |
| `PixelEquivalence` | `opencv_opentrackio_proofs/PixelEquivalence.lean` | 2 (imports `PrincipalPointConversion`) |
| `HarnessAdapter` | `opentrackio_parser/HarnessAdapter.lean` | 25 (full decoder chain via `SampleDecoder`) |

28 unique files total (`DistortionConversion.lean:1-45`,
`PrincipalPointConversion.lean:1-66`, `PixelEquivalence.lean:38-39` — only imports
`Mathlib.Tactic` and `PrincipalPointConversion` — and `HarnessAdapter.lean:14`'s decoder
closure). **None of the following are reached by plain `lake build`:**

- `opencv_opentrackio_proofs/Pipeline/*.lean` (6 files, including `PixelIff.lean`,
  `PixelIffCorrected.lean`, `PixelSufficiency.lean`, `OpenCVModel.lean`,
  `RadialPipeline.lean`) — **so `opencv_openlensio_full_pipeline_pixel_iff` itself is
  never type-checked by the documented build command.**
- `opencv_opentrackio_proofs/DistortionConversionCorrected.lean`,
  `opencv_opentrackio_proofs/MutationTests.lean` — the "corrected" tangential theorem and
  all 34 mutation tests are never checked by `lake build`.
- All 12 files of `openlensio_semantics/` — **so `undistortPoint_injective_pure_radial`
  (`InjectivityModel.lean`) is never type-checked by the documented build command.**
- `inverse_approximation/InverseApproximation.lean` — **so `D_exists_unique_preimage`,
  `inverse_approx_error`, and every other inverse-approximation theorem is never
  type-checked by the documented build command.**
- 19 `opentrackio_parser/` files not reachable from `HarnessAdapter`'s decoder-only
  closure, including **every encoder** (`CameraEncoder.lean`, `LensEncoder.lean`,
  `SampleEncoder.lean`, `TransformEncoder.lean`, etc.), `WellFormedSampleJson.lean`, and
  `NormalizationTheorems.lean` — **so `encodeSample_roundtrip`,
  `sampleNormalize_idempotent`, and `normalization_under_wellFormed` are never type-checked
  by the documented build command**, despite being listed as the parser's three headline
  "Key properties proved" in `README.md:87-95`.

**Empirical test 3 (does it actually compile?).** All 63 `lean_lib` targets were built
explicitly: `lake build InverseApproximation DistortionConversion ... InjectivityModel`
(full list in the command log). Result: `Build completed successfully (8382 jobs)`, exit
0, real time 4m30s. Output contained only linter warnings (`unused variable`, `unused simp
argument`) and `#eval`/`#print`-style `info:` trace lines from `IntegrationSmoke.lean` and
`ExecutableSemanticOracle.lean` — no errors, no `sorry` warnings, no axiom warnings beyond
the expected set (§2.4).

**Conclusion:** this is a genuine reproducibility defect — the documented verification
procedure silently verifies well under half the repository, and specifically excludes
every theorem the task brief and the README itself identify as the project's central
claims — but it is a *Lake configuration* defect, not a *proof* defect. The code behind
the gap is correct.

**Required action:** add the 59 missing `lean_lib` names to `defaultTargets` in
`lakefile.toml:3` (or restructure into a small number of umbrella libraries with
exhaustive `globs`), and update `README.md:208`'s expected job count accordingly (it
should read ~8382, not "low thousands," once default coverage is fixed — "low thousands"
is accurate for the *current*, truncated default build, which undersells how much is
actually proved). CI (if any) should be checked for whether it already passes explicit
target names; if it only runs plain `lake build`, it has never verified the headline
theorems either.

### 2.2 Compatibility re-export gap (related, minor)

`opencv_opentrackio_proofs/PipelineEquivalence.lean:9-13` imports `Pipeline.OpenCVModel`,
`Pipeline.RadialPipeline`, `Pipeline.PixelSufficiency`, `Pipeline.PixelIffHelpers`, and
`Pipeline.PixelIff` — but **not** `Pipeline.PixelIffCorrected`. A reader who does
`import PipelineEquivalence` (the file's own doc-comment calls it a "Compatibility
re-export. All declarations live in Pipeline/.") will not get
`opencv_openlensio_full_pipeline_pixel_corrected` or
`physical_pixel_agreement_scale_independent_example` in scope, and would need to know to
`import Pipeline.PixelIffCorrected` directly. Low severity, but worth fixing alongside
§2.1 since the two are adjacent symptoms of the same "umbrella import doesn't actually
umbrella" pattern.

### 2.3 Forbidden-construct scan

```sh
grep -rEn --include="*.lean" "sorry|admit|native_decide|^unsafe|^partial" . --exclude-dir=.lake
grep -rEn --include="*.lean" "^\s*axiom\b" . --exclude-dir=.lake
```

Results:
- **No** `sorry`, `admit`, custom `axiom`, `unsafe`, or `partial` declarations anywhere in
  the first-party source tree. The only string matches are doc-comments *asserting their
  absence* (`HarnessAdapter.lean:10`: "No new proofs. No sorry, admit, axiom, unsafe,
  partial."; `SemanticBridge.lean:21`: "do not add a sorry.") and one genuine
  `native_decide` use (next section).
- `set_option maxHeartbeats` appears in four encoder files (`CameraEncoder.lean:56`,
  `LensEncoder.lean:229,247`, `SampleEncoder.lean:203`, `TimingEncoder.lean:29`) — these
  raise the elaboration timeout, not a trust-weakening option; harmless.

### 2.4 `#print axioms` on headline declarations

Run via `lake env lean` against a scratch file importing the relevant modules (not
`#eval`/test output — actual kernel axiom dependency reports):

```
'opencv_openlensio_full_pipeline_pixel_iff'              → [propext, Classical.choice, Quot.sound]
'opencv_openlensio_full_pipeline_pixel_corrected'         → [propext, Classical.choice, Quot.sound]
'physical_pixel_agreement_scale_independent_example'      → [propext, Classical.choice, Quot.sound]
'undistortPoint_injective_pure_radial'                    → [propext, Classical.choice, Quot.sound]
'undistortPoint_injective_zero_tangential'                → [propext, Classical.choice, Quot.sound]
'undistortPoint_injective_on_circle_tangential'            → [propext, Classical.choice, Quot.sound]
'D_exists_unique_preimage'                                → [propext, Classical.choice, Quot.sound]
'inverse_approx_error'                                     → [propext, Classical.choice, Quot.sound]
'D_injective_on_disk'                                       → [propext, Classical.choice, Quot.sound]
'encodeSample_roundtrip'            → [propext, Classical.choice, Quot.sound,
                                        encodeVersionDigit_roundtrip._native.native_decide.ax_1_{1..10}]
'sampleNormalize_idempotent'        → same as above (10 native_decide axioms)
'normalization_under_wellFormed'    → same as above (10 native_decide axioms)
```

`propext`, `Classical.choice`, `Quot.sound` are Lean 4's three standard foundational
axioms (propositional extensionality, choice, quotient soundness), present in essentially
every nontrivial Mathlib-based development; they are not a defect and are not
project-specific trust extensions.

The `native_decide` dependency is real and worth naming explicitly: `VersionEncoder.lean:43`
(`fin_cases d <;> native_decide`) uses `native_decide` rather than `decide` because, per
the file's own comment (`VersionEncoder.lean:27-32`), plain `decide` gets stuck —
`native_decide` compiles the decidability instance to native code and runs it, trusting
Lean's code generator and FFI boundary rather than only the kernel's definitional
reduction. This is a standard, narrowly-scoped, and *disclosed-in-comment* use, not a
hidden trust gap — but it is not mentioned in `docs/limitations.md`'s discussion of what
is and isn't proved, and it means `encodeSample_roundtrip`,
`sampleNormalize_idempotent`, and `normalization_under_wellFormed` sit on a strictly
larger trust base than the pipeline/semantics/injectivity/inverse-existence theorems
above them. This should be a one-line addition to `docs/limitations.md`'s parser section,
not a blocker.

### 2.5 Default-target build is self-consistent (positive finding)

To be clear this is not "the code doesn't work": plain `lake build` succeeds (exit 0,
`Build completed successfully (3316 jobs)`) and the *explicit full build* also succeeds
(exit 0, `8382 jobs`, only linter warnings). There is no partial-build failure, no
divergent behavior between incremental and clean builds, and no evidence of code that
only "looks" like it compiles. The defect is purely that the default target list is a
small, undocumented subset of what the repository actually contains and claims.

---

## 3. Theorem-by-theorem assumption audit

### 3.1 `opencv_openlensio_full_pipeline_pixel_iff` (`opencv_opentrackio_proofs/Pipeline/PixelIff.lean:29-74`)

**Exact statement** (elaborated): for all reals `k1..k6, p1, p2, l1..l6, q1, q2, fx, cx,
ws, w, F, ΔPx`, given
- `hw : w ≠ 0`, `hws : ws ≠ 0`, `hF : F ≠ 0`, `hF_pos : 0 < F` — **technical** (nonzero
  denominators / positivity needed for later division and sign reasoning),
- `hl1..hl6 : lᵢ = kⱼ/F^(2n)` (6 equations) — **representation**: the as-published
  radial coefficient conversion, assumed as context, not derived here,
- `hq1, hq2 : qᵢ = pᵢ/F²` — **representation**: the as-published (uncorrected)
  tangential conversion,
- `hF_eq : F = (w/ws)·fx`, `hΔPx : ΔPx = (w/ws)·(cx − ws/2)` — **representation**: the
  as-published focal-length/offset conversion,
- `hp : p1 ≠ 0 ∨ p2 ≠ 0` — **domain/physical**: rules out the pure-radial case; see
  §3.1.1,
- `hden : ∀ x' y', 1 + k4(x'²+y'²) + k5(...)² + k6(...)³ ≠ 0` — **domain**: free,
  universally-quantified nonvanishing-denominator hypothesis; see §3.1.2,

the conclusion is: `(∀ x' y', OpenCV_pixel_x(x',y') = OpenTrackIO_pixel_x(x',y')) ↔ ws/w = fx`.

**Classification check — does the conclusion follow almost immediately from the
hypotheses?** No. The hypotheses fix *how* the coefficients relate (`l,q` as functions of
`k,p,F`); they do **not** assume `ws/w = fx`, and they do not assume pixel agreement. The
↔ is the actual content: both directions are proved from the coefficient-conversion
hypotheses, not smuggled in. The `→` direction (`PixelIffHelpers.lean`:
`pixel_eq_implies_tangential_gap` then `tangential_gap_forces_scale`) genuinely uses `hp`
to find a point where the tangential term is nonzero and extract `ws/w = fx` by
cancellation — this is real algebraic content, not restated hypothesis.

**3.1.1 — `hp : p1 ≠ 0 ∨ p2 ≠ 0` is a real restriction, honestly disclosed.** When both
tangential coefficients are zero, the ↔ is **false as an iff** in the useful direction:
pixel agreement no longer entails `ws/w = fx` (the tangential term that reveals the scale
mismatch vanishes identically), yet the theorem's hypotheses would still type-check. This
is disclosed in `docs/limitations.md:94-98` ("Pure-radial case not characterized") and
`docs/specification-questions.md` SQ-CV-01 (status: open). **This is correctly scoped,
not an overclaim** — but it does mean the theorem proves something about lenses with
tangential distortion specifically, not "any" lens, and the README's one-line summary
("the x-pixel outputs agree for all normalised inputs if and only if `ws/w = fx` (given
all coefficient conversions hold)", `README.md:43`) does not repeat the `hp` caveat
in-line — a reader of the README summary alone would not know this. Low-severity
documentation gap; the caveat exists, just not adjacent to the headline sentence.

**3.1.2 — `hden` is a free (undischarged) hypothesis, honestly disclosed.** Every pipeline
theorem assumes the radial rational function's denominator is nonzero at *every* point, as
an opaque universally-quantified hypothesis rather than derived from bounds on `k4,k5,k6`.
Disclosed as SQ-OL-01/SQ-CV-02 (both status: open). This is standard practice for a
rational-function model (the spec itself is silent on the zero-denominator case — see
§4), but it does mean the theorem is conditional on a side-condition that is not shown to
be satisfiable by any concrete, physically-realistic coefficient set within this proof
(though `radialTerm_pos`/`radialTerm_ne_zero` in `InjectivityModel.lean:184-199` *do*
provide a constructive per-point discharge elsewhere in the repo, via `hNum, hDen`
positivity — that discharge is not wired into the pipeline-iff theorems).

**Verdict: not vacuous, not circular, genuinely a conditional-iff theorem whose
conditions are disclosed (if not always adjacent to the headline summary). Proves a
same-direction (U→D) coordinate-conjugacy fact about the formal model — not, by itself, a
claim about any specific external renderer or implementation.**

### 3.2 `opencv_openlensio_full_pipeline_pixel_corrected` (`Pipeline/PixelIffCorrected.lean:71-132`)

Same hypothesis shape as §3.1 except `hq1, hq2 : qᵢ = pᵢ/F` (one power of `F` lower) and
**no `hp` hypothesis at all** — conclusion is unconditional pixel agreement for all
`x', y'`, no `ws/w = fx` side-condition.

**Is this theorem's un-conditionality suspicious (i.e., does removing `hp` and the ↔
side-condition smuggle in the result)?** No — verified independently by direct symbolic
substitution (§4): with `q = p/F`, the tangential term's extra `F` factor from the
`(F·x')(F·y')` argument is exactly cancelled by the `1/F` in `q`, leaving a term that
scales by the *same* single factor of `F` that the radial term already carries via its
`(F·x')` multiplier — so `(ws/w)·F = fx` (an **identity**, given `hF_eq`, not a side
condition) makes both the radial and tangential parts match unconditionally. This is a
real, checkable algebraic fact, not a restated hypothesis; `ring`/`field_simp` close the
goal after substitution (`PixelIffCorrected.lean:120-132`), and the Lean kernel has
verified it.

**Claim-scope discipline (strong, positive finding):** this file is unusually explicit
about what it does *not* claim. Lines 48-68 and 134-151 state, in-file, that this is a
"same-direction coordinate-conjugacy result," not a claim that OpenLensIO native (D→U)
undistortion consumption of the converted coefficients is correct — and cross-reference
`docs/specification-questions.md` SQ-CV-07 and `docs/limitations.md`. This scope
discipline is maintained consistently across the README, limitations.md, and the
in-file comments; I did not find a location where this caveat is dropped in a
public-facing summary (checked `README.md:45-55`, `docs/opentrackio-proof-summary.md:7`).

**`physical_pixel_agreement_scale_independent_example` (`PixelIffCorrected.lean:154-196`)**
is a concrete existential witness (`fx=1, ws=2, w=1 ⟹ F=1/2, ws/w=2≠fx=1`, pure tangential
lens `p1=1`) proving pixel agreement holds even though `ws/w ≠ fx` under the corrected
hypotheses — a genuine counterexample to the naive port of the uncorrected iff, not a
restatement of the corrected theorem. This is good practice: it demonstrates the
side-condition genuinely vanishes rather than merely "not yet proved to be required."

**Verdict: sound, unconditional, correctly scoped as a coordinate-conjugacy result.**

### 3.3 `undistortPoint_injective_pure_radial` (`openlensio_semantics/InjectivityModel.lean:126-168`)

**Exact statement:** given `p.p1 = 0`, `p.p2 = 0` (pure radial), `hR₁ : radialTerm k
(sensorRadius ε₁) h₁ ≠ 0`, and the caller-supplied
`hScaleInj : ∀ r₁ r₂ ≥ 0, (radialScale k r₁)²·r₁² = (radialScale k r₂)²·r₂² → r₁ = r₂`,
then `undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂ → ε₁ = ε₂`.

**Does `hScaleInj` smuggle in the 2-D injectivity conclusion?** This is the right
question to ask of any injectivity theorem with a caller-supplied injectivity hypothesis.
Here the answer is **no, correctly classified**: `hScaleInj` is injectivity of a
**1-dimensional scalar function** `r ↦ R(r)²·r²` on `[0,∞)`, strictly weaker than and
logically prior to the 2-D claim being proved (2-D injectivity of the vector map
`undistortPoint`). The proof (`InjectivityModel.lean:136-168`) does real work reducing the
2-D problem to the 1-D one: square both component equalities, add them via
`sensorRadius² = x²+y²`, invoke `hScaleInj` once to recover `sensorRadius ε₁ = sensorRadius
ε₂`, then reduce to the on-circle case (`undistortPoint_injective_zero_tangential`). This
is legitimate hypothesis-reduction, not restated-conclusion.

**Is `hScaleInj` left as a permanently opaque, undischarged hypothesis?** No —
`radialScale_hScaleInj` (`InjectivityModel.lean:426-453`) constructively discharges it
under an explicit, checkable "sign-separation" coefficient condition
(`k1,k3,k5 ≥ 0 ∧ k2,k4,k6 ≤ 0`) plus `hdenPos` (denominator strictly positive for all
`r ≥ 0`), via a genuine analytic argument: `radialScale_mul_derivPos` computes the
derivative of `r ↦ R(r)·r` using Mathlib's `HasDerivAt` quotient rule and shows it is
strictly positive on `(0,∞)` under the sign constraints (`InjectivityModel.lean:332-387`),
then `radialScale_mul_strictMono` lifts this to `StrictMonoOn` via
`strictMonoOn_of_deriv_pos` (`:398-416`), and `radialScale_hScaleInj` concludes injectivity
from strict monotonicity via `StrictMonoOn.injOn` plus a sign-based square-root step
(`:426-453`). This is real analysis (derivatives, continuity, strict monotonicity), not
algebra dressed up — a notable strength of this file.

**Verdict: hypothesis correctly classified as a logically-prior, strictly-weaker fact;
constructively dischargeable under disclosed, checkable coefficient conditions. Not
circular, not vacuous.**

Two scope caveats, both honestly disclosed in-file (`InjectivityModel.lean:1-43`) and in
`docs/limitations.md:55-60`: this proves **injectivity**, not **invertibility**
(surjectivity onto the intended output range and continuity are explicitly not proved —
SQ-OL-07, status open), and the companion on-circle-with-full-tangential theorem
(`undistortPoint_injective_on_circle_tangential`, `:233-286`) requires a caller-supplied
nonvanishing-determinant hypothesis (`hDet`) on a 2×2 linear system built from the
tangential coefficients — also correctly classified as a real, non-circular technical
condition (the determinant structure is derived explicitly in the comment at `:201-230`,
not asserted by fiat).

### 3.4 Inverse approximation / contraction hypotheses (`inverse_approximation/InverseApproximation.lean`)

**Model-fidelity finding (disclosed, not hidden, but worth stating plainly for this
audit):** `InverseApproximation.lean` works over a **structurally different model** from
the rest of the repository. Its `Coeffs` (`:35-40`) has only 3 radial coefficients
(`k1,k2,k3`, no denominator) and 2 tangential (`p1,p2`) — a pure **polynomial** map
`Φ : ℂ → ℂ`, whereas the actual OpenLensIO/OpenCV Brown-Conrady model used everywhere
else in the repo (`RadialCoefficients` in `openlensio_semantics/LensSemantics.lean`,
`DistortionConversion.lean`'s `k1..k6`) is a **rational function** (6 coefficients,
numerator/denominator). This is explicitly and repeatedly disclosed in-file (`:20-22`:
"Deliberately independent of `opencv_opentrackio_proofs/` and `openlensio_semantics/`: no
imports from either") and in every theorem's doc-comment ("Scope: polynomial
(non-rational) Brown-Conrady model only"). **This audit confirms the disclosure is
accurate and not contradicted elsewhere**: `README.md` does not mention
`inverse_approximation/` at all in its top-level section breakdown (it describes "four
projects" — `opencv_opentrackio_proofs`, `opentrackio_parser`, `openlensio_semantics`,
`battery-tester` — omitting `inverse_approximation` as a named section), and
`docs/specification-questions.md` SQ-CV-07's "Current status" paragraph (`:226-240`)
states plainly that `D_exists_unique_preimage` "does NOT resolve" the D-U/U-D
interoperability question and is "a standalone mathematical fact about the polynomial
model." No overclaim found here.

**`D_exists_unique_preimage` (`:596-642`) hypothesis audit:** given `hR : 0 ≤ R`,
`hcontract : |t|·L θ R < 1`, and `hy : ‖y‖ + |t|·M θ R ≤ R`, concludes
`∃! z, ‖z‖ ≤ R ∧ D θ t z = y`. `hcontract` is a genuine Banach-contraction sufficient
condition (not shown necessary — disclosed at `:591-593`: "remains a SUFFICIENT
contraction threshold (not shown necessary)"), and `hy` is a disclosed "buffer" condition
ensuring the iteration stays inside the disk. The proof (`:596-642`) is a real application
of Mathlib's `ContractingWith.exists_fixedPoint'` to the closed disk via
`IsClosed.isComplete`, not a restatement. **Correctly scoped, not vacuous, not circular.**
The theorem is a legitimate standalone existence/uniqueness result; its *relevance* to the
OpenTrackIO interoperability question is, as disclosed, separate and unestablished.

### 3.5 Parser roundtrip / well-formedness (`opentrackio_parser/`)

**`encodeSample_roundtrip` (`opentrackio_parser/SampleEncoder.lean:205-...`):**
`∀ s : Sample, decodeSample (encodeSample s) = .ok s`. This is a genuine universally-
quantified structural theorem, not test-sampled: the proof destructures every optional
field of `Sample` via `rcases ... with _ | _ <;> ...` across 10 optional sub-fields
(`:208-219`) before closing with `simp`, i.e. it is proved by exhaustive case analysis
over the *type*, not over a finite list of example JSON fixtures. **Not test-suite
overfitting.**

**`normalization_under_wellFormed` / `wellFormed_normalize_eq_encode`
(`NormalizationTheorems.lean:55-64`) — unused hypothesis (P1 finding):**

```lean
theorem wellFormed_normalize_eq_encode (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    sampleNormalize j = encodeSample s := by
  simp only [sampleNormalize, hd]

theorem normalization_under_wellFormed (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    decodeSample (sampleNormalize j) = .ok s := by
  simp only [sampleNormalize, hd, encodeSample_roundtrip]
```

Both hypotheses are bound as `_` (anonymous, unused — confirmed by inspection of the
proof terms, which reference only `sampleNormalize`, `hd`, and `encodeSample_roundtrip`).
**The `WellFormedSampleJson j` hypothesis does no logical work in either proof.** Both
theorems are true unconditionally whenever `decodeSample j = .ok s` holds — i.e. the
actual content is "if `j` already decodes successfully to `s`, normalizing it still
decodes to `s`," which has nothing to do with schema well-formedness as such (it follows
directly from `encodeSample_roundtrip` plus the definition of `sampleNormalize` as
"decode, and on success re-encode"). This contradicts the framing in `README.md:92-93`
("`normalization_under_wellFormed` — normalization preserves decoded semantics for
well-formed inputs") and the comment at `NormalizationTheorems.lean:60` ("for
schema-clean JSON that decodes to s, normalization also decodes to s") — both suggest
well-formedness is doing real work, when the Lean proof shows it is not. This is a
**comment/formal mismatch and an unused-hypothesis finding**, not a correctness defect —
the theorem as stated is still true — but readers citing "normalization is proved safe
for well-formed inputs" as evidence would be citing a hypothesis that isn't actually load-
bearing in the cited theorem.

**Required action:** either (a) drop the unused hypothesis and restate both theorems in
terms of `decodeSample j = .ok s` alone (the true, more general fact), or (b) if
well-formedness is intended to matter for some reason not captured by the current proof
(e.g. a future strengthening), add a comment explaining why the hypothesis is present but
currently redundant. Do not leave the current framing, which implies the precondition is
necessary when the kernel-checked proof shows it is not used.

---

## 4. Specification-to-definition traceability matrix

Primary sources located and read directly (not inferred from repository paraphrase):
`docs/OpenCV_to_OpenTrackIO.pdf` (3 pages, "Conversion of OpenCV to OpenTrackIO
(OpenLensIO) lens calibration parameters," corrected 2025-09-02) and, as of the
hostile-review pass in §4.1, `docs/OpenLensIO_v1-0-1.pdf` in full (10 pages, "OpenLensIO
Lens Model Version 1.0.0," 17 February 2025) — used as the authoritative source for the
`U` function definition (Eq.16-17), the `ε'_u = F·x'` coordinate identity (Eq.9), and the
units/direction of OpenLensIO's native `k,p` coefficients, rather than relying only on the
conversion paper's restatement of these.

| Claim | Normative source (equation) | Lean definition | Units/convention | Direction | Hidden assumptions | Status |
|---|---|---|---|---|---|---|
| Radial conversion `l1=k1/F², l3=k2/F⁴, l5=k3/F⁶` (numerator); `l2=k4/F², l4=k5/F⁴, l6=k6/F⁶` (denominator) | PDF p.2-3, "Comparing individual components... $k_1 r^2 = l_1 r_u^2 = l_1 F^2 r^2$" | `DistortionConversion.lean:57-66` (`radial_distortion_conversion`, generic over `n`), instantiated at n=1,2,3 | OpenCV normalized coords `(x',y')` vs OpenTrackIO screen coords `(ε'_u = F·x')` | U→D (both sides describe the undistorted→distorted multiplicative factor) | None found — transcription matches the PDF verbatim, including the structure of the derivation (term-by-term match after substituting `r_u = F·r`) | **Established** — verified against primary source, not just repository paraphrase |
| Tangential conversion `q1=p1/F², q2=p2/F²` (as-published) | PDF p.3, "$p_1 x' y' = q_1 \epsilon'_{x,u}\epsilon'_{y,u} = q_1 F x' F y' \Rightarrow q_1 = p_1/F^2$" | `DistortionConversion.lean` `tangential_q1_conversion`/`tangential_q2_conversion`; consumed by `PixelIff.lean:36` (`hq1,hq2`) | same | U→D | **The paper's own term-by-term matching treats the additive tangential displacement the same way it treats the multiplicative radial factor — see dimensional-analysis finding below** | **Disputed — independently re-derived, see below** |
| Focal length / principal point `F = (w/ws)·fx`, `ΔPx = (w/ws)·(cx − ws/2)` | PDF p.2, "Focal length and projection offset parameters" | `PixelIff.lean:33,37` (`hF_eq`, `hΔPx`) | pixel ↔ screen-shader units via `w/ws` ratio | — | None found — transcription matches verbatim, including the corrected `−w_shader/2` term the paper itself flags as a prior-version bug (PDF p.2, "Note that in a previous version... was missing") | **Established** |
| Corrected tangential `q1=p1/F, q2=p2/F` | Not in the PDF — repository's own re-derivation (`docs/specification-questions.md` SQ-CV-06) | `DistortionConversionCorrected.lean`; consumed by `PixelIffCorrected.lean:78` | same | U→D | Repository-internal derivation, not yet confirmed by the paper's authors | **Open — maintainer response pending (sent 2026-08-15)**; independently supported by this audit's dimensional analysis (below), not yet independently confirmed by a reference implementation or the paper's authors |
| Pipeline theorems compare U→D formula shape on both sides | PDF defines `ε'_{x,d} = F·x''` (p.2) — i.e. relates *distorted* coordinates, which is what the Lean pipeline theorems reproduce | `Pipeline/PixelIff.lean:42-57`, `Pipeline/PixelIffCorrected.lean:83-100` | — | **Both sides U→D** — this is what the PDF's own equations describe | Separately, the OpenTrackIO *JSON schema*'s `distortion.model` field defaults to `"Brown-Conrady D-U"` (opposite direction) when omitted — this is a schema-level question, not a question about whether the Lean theorems faithfully formalize the PDF's U→D equations (they do) | **Established that the Lean theorems match the PDF's U→D equations; separately open whether a real producer/consumer is expected to tag `model="Brown-Conrady U-D"` for these coefficients to apply correctly — SQ-CV-07, maintainer response pending** |

### 4.1 Independent dimensional analysis: is `q=p/F²` or `q=p/F` consistent with the paper's own definitions?

This section was extended in a follow-up hostile-review pass whose explicit goal was to
*disprove* the finding below — to reconstruct both formulas from scratch, consider every
plausible alternative interpretation (specification error / convention difference /
forward-inverse mismatch / repository misreading), and try especially hard to find a
coherent reading under which the published `q=p/F²` is correct. It could not be found.
The analysis below is organized into (a) an independently-reconstructed reading of both
primary sources, (b) two independent derivations of the required scaling, (c) two
hand-verifiable numeric counterexamples, (d) the alternative interpretations considered
and why each was rejected, and (e) a precisely-scoped verdict. **No step below relies on
the Lean proof as evidence** — every claim is re-derived from the two PDFs and ordinary
algebra, independently of `DistortionConversionCorrected.lean`.

#### 4.1.1 Independent reconstruction from both primary sources

Two documents are authoritative here, not one. The conversion paper
(`docs/OpenCV_to_OpenTrackIO.pdf`) states the coordinate relations used below; the base
specification (`docs/OpenLensIO_v1-0-1.pdf`) defines the distortion formula those
relations apply to, and was read in full for this pass (not merely cited secondhand).

- **OpenCV** (p.1 of the conversion paper, cross-checked against the standard
  `docs.opencv.org/.../calib3d` Brown-Conrady model, independently known, not sourced from
  this repository): normalized pinhole coordinates `x'=X/Z, y'=Y/Z` (dimensionless);
  forward distortion `x'' = R_cv(r)·x' + T_cv(x',y')`, `T_cv(x',y')=2p1x'y'+p2(r²+2x'²)`;
  pixel mapping `u=fx·x''+cx` with `fx,cx` in pixels, applied *after* distortion.
- **OpenLensIO** (`OpenLensIO_v1-0-1.pdf` §4.1, Eq.16-17 — the *authoritative* definition,
  not the conversion paper's paraphrase of it):
  `U(ε)_x = R(r)·εx + 2p1·εxεy + p2(r²+2εx²)`, `r=|ε|` in **mm**, with `p1,p2` explicitly
  documented as having units `mm⁻²` (§4.1, units table). `U` is stated to map
  **distorted→undistorted** (D→U) coordinates. The spec states explicitly (Eq.5, Eq.11)
  that the forward map `U⁻¹` ("formerly named D") has **no closed form** — inversion
  requires numerical iteration. The conversion paper's `l,q` are therefore not literally
  `U⁻¹`'s exact coefficients; they are a same-*shape*, independently-parameterized
  approximation to the forward map, evaluated at the undistorted screen point.
- **The coordinate identification is authoritative, not the conversion paper's invention**:
  OpenLensIO Eq.9 (base spec) defines `ε'_u = F·[x,y]_u` directly — the conversion paper's
  `ε'_{x,u}=F·x'`, `ε'_{x,d}=F·x''` (p.2) are a restatement of this, not a separate,
  weaker claim introduced only by the paper being audited.
- **Direction check (resolves interpretation C up front, see §4.1.4):** both `R_cv(r)·x'+T_cv(x',y')`
  (OpenCV) and `R_oti(r_u)·ε'_u+T_oti(ε'_u)` (the paper's `D`, same shape as OpenLensIO's
  `U` in Eq.16-17 but evaluated at the *undistorted* argument) are forward, U→D
  evaluations. There is no forward/inverse confusion in the comparison itself — both
  sides apply the same formula shape in the same direction. What remains genuinely open
  is a *different* question, addressed in §4.1.5 and unchanged by this section: whether a
  real consumer reading `distortion.model="Brown-Conrady D-U"` (OpenLensIO's *native* `U`,
  using a third, separate coefficient set in mm units) is doing the same thing a producer
  who emitted `l,q` via this conversion intended.

#### 4.1.2 Two independent re-derivations of the required scaling

**Derivation 1 — direct substitution into the stated coordinate identity.** Requiring
`ε'_{x,d} = F·x''` to hold for arbitrary, independently-chosen radial and tangential
coefficients (both are free parameters of the model) forces it to hold termwise:

```
R_oti(r_u)·F·x'     =  F·R_cv(r)·x'       ⟹  R_oti(r_u) = R_cv(r)                  (*)
T_oti(F·x', F·y')   =  F·T_cv(x',y')                                                (**)
```

`(*)` is exactly what the paper derives for radial coefficients (p.2-3: `k1r²=l1r_u²`,
giving `l=k/F^{2n}`) — correct, because `R` is a dimensionless multiplicative factor and
the single `F` already present in `ε'_u=F·x'` accounts for everything. `(**)` requires
**one explicit additional factor of `F`** beyond what the coordinate substitution
contributes, because `T` is an *additive* displacement, not a multiplicative scale.
Substituting `T_oti(ε_x,ε_y)=2q1ε_xε_y+q2(ε_x²+ε_y²+2ε_x²)` with `ε_x=Fx',ε_y=Fy'` gives
`T_oti(Fx',Fy') = F²·T_cv^{q→p slot}(x',y')`, so `(**)` becomes `F²q=F·p`, i.e.

```
q1 = p1/F,   q2 = p2/F
```

**Derivation 2 — function conjugation under coordinate scaling** (a structurally
different method, with no reference to pixels, `cx`, or focal length at all — a pure
check of what "the same map, re-expressed in `F`-scaled coordinates" must mean). Define
`g = S_F ∘ f ∘ S_F⁻¹` where `S_F(z)=Fz`, i.e. `g(y) = F·f(y/F)`. This is the generic,
model-independent statement of "the same underlying distortion, described in coordinates
`F` times larger." For the multiplicative radial part, `F·R(y/F)·(y/F) = R(y/F)·y`,
reproducing `l=k/F^{2n}` directly. For the additive, homogeneous-degree-2 tangential part
`T(x)`, `F·T(y/F) = F·(1/F²)·T(y) = T(y)/F` — so `g`'s tangential coefficient is
`p/F`, matching Derivation 1 by a completely independent route.

**Why the paper's own method is correct for radial and wrong for tangential.** The paper's
actual method is literal value-matching (`k1r² = l1·r_u²`). This happens to work for the
radial term because that term multiplies a coordinate (`εu=Fx'`) that itself already
carries the missing `F`, so matching the bare term-value automatically makes the *full
contribution* (term × coordinate) scale correctly. The tangential term is added directly,
with no such implicit multiplication to supply the missing factor — so matching bare
term-values leaves the contribution under-scaled by exactly one power of `F`. This is a
specific, checkable structural reason, not a generic "something seems off."

**The `F=1` diagnostic.** The published (uncorrected) theorem's own necessary-and-sufficient
condition, `ws/w = fx`, is algebraically identical to `F=1` (`F=(w/ws)fx`, so
`ws/w=fx ⟺ F=1`). At `F=1`, `F²=F`, so the one-power-of-`F` discrepancy is numerically
invisible. The paper's own worked focal-length derivation (p.2) never instantiates the
distortion formula with concrete nonzero tangential coefficients at `F≠1` to cross-check
— there is no point in the paper's own working where this discrepancy would have
surfaced.

#### 4.1.3 Two hand-verifiable numeric counterexamples

Computed directly from the published formulas (conversion paper p.1-3 and OpenLensIO
Eq.16-17), not from the repository's Lean code, and checkable with a calculator.

**Example 1.** `fx=10, cx=0, w=2, ws=4 ⟹ F=(w/ws)·fx=5`. Pure tangential lens:
`p1=1, p2=0`, all radial coefficients `0`. Point `x'=1, y'=1`.
- OpenCV: `x''=1·1+2·1·1·1=3`, `u_cv=fx·x''+cx=10·3=30`.
- Corrected (`q1=p1/F=0.2`): `ε'_u=(5,5)`, `ε'_{d,x}=5+2(0.2)(25)=15`,
  `ΔPx=(w/ws)(cx-ws/2)=(0.5)(-2)=-1`, `u_oti=(ws/w)(15-1)+ws/2=2·14+2=30`. **Matches `u_cv=30`.**
- Published (`q1=p1/F²=0.04`): `ε'_{d,x}=5+2(0.04)(25)=7`, `u_oti=(2)(7-1)+2=14`.
  **Does not match (`14≠30`).**

**Example 2** (different coefficient, nonzero `cx`, different `F`). `fx=7, cx=4, w=3,
ws=6 ⟹ F=3.5`. Pure tangential: `p2=1, p1=0`. Point `x'=2, y'=1` (`r²=5`).
- OpenCV: `x''=2+1·(5+2·4)=15`, `u_cv=7·15+4=109`.
- Corrected (`q2=p2/F=2/7`): `ε'_u=(7,3.5)`, `r_u²=61.25`,
  `ε'_{d,x}=7+(2/7)(61.25+98)=52.5`, `ΔPx=(3/6)(4-3)=0.5`,
  `u_oti=(6/3)(53.0)+3=109`. **Matches `u_cv=109`.**
- Published (`q2=p2/F²=1/12.25`): `ε'_{d,x}=7+13=20`, `u_oti=(2)(20.5)+3=44`.
  **Does not match (`44≠109`).**

Both examples confirm the pattern predicted by §4.1.2: the corrected scaling reproduces
OpenCV's pixel output exactly, unconditionally (including at `ws/w≠fx`, i.e. `F≠1`); the
published scaling only reproduces it when `F=1`, where the discrepancy is invisible by
construction.

#### 4.1.4 Alternative interpretations considered and rejected

Checked explicitly, in response to the instruction to try hard to make the published
formula correct:

- **B (coordinate-normalization / parameter-meaning difference).** Checked whether `ε'_u`
  might use a different scale than `F·x'`, or whether OpenLensIO's `p1,p2` (native, mm⁻²,
  used in `U`) might be the *same* numbers the conversion paper calls `q1,q2` under a
  different unit convention that would rescue `F²`. Rejected: OpenLensIO Eq.9 gives
  `ε'_u=F·x'` as the sole authoritative definition, with no alternative scale convention
  stated anywhere in either document; and the conversion paper's own coefficient table
  explicitly maps OpenCV's *forward* `k,p` onto `l,q` (not onto OpenLensIO's native,
  undistortion-side `k,p`), so `l,q` and OpenLensIO's native `k,p` are deliberately
  different coefficient sets for different functions, not a unit-relabeling of the same
  numbers.
- **C (forward/inverse convention mismatch).** Checked whether the comparison itself
  might be comparing a forward map to an inverse map. Rejected for *this specific
  derivation*: both sides of the comparison in §4.1.1-4.1.2 are U→D (forward)
  evaluations, confirmed directly from OpenLensIO's own Eq.16-17 and the conversion
  paper's stated purpose. This does **not** resolve the separate, still-open question of
  whether the *resulting* `l,q` coefficients, if consumed via the JSON schema's
  `distortion.model="Brown-Conrady D-U"` default (OpenLensIO's *native* `U`, a different
  function using a different, unconverted coefficient set), behave as intended — see
  §4.1.5 and the explicit non-resolution note below.
- **D (repository misreading of the paper).** Checked whether this repository's own
  transcription of the paper (`DistortionConversion.lean:1-43`) might itself be the error,
  rather than the paper. Rejected: the transcription matches the PDF's stated equations
  verbatim, including the structure of the per-term derivation; the inconsistency traced
  above is present in the PDF's own text (p.2 vs. p.3), not introduced by the repository's
  restatement of it.
- **Cross-check against real implementations.** `ris-osvp-metadata-camdkit` (Python) and
  `opentrackio-cpp` (C++) were both inspected directly (not via this repository). Neither
  implements this conversion: both store `lens.distortion[].tangential` as an opaque
  tuple/vector of numbers, with no code path that computes `l,q` from OpenCV `k,p` or
  vice versa. **This is a genuine null result, not a confirmation either way** — there is
  currently no production code anywhere in the ecosystem whose behavior would be affected
  by resolving this question, and no implementation to check either formula against.

No interpretation was found under which the published `q1=p1/F², q2=p2/F²` is consistent
with the coordinate relations (`ε'_u=F·x'`, `ε'_{x,d}=F·x''`) that both primary-source
documents state as authoritative.

#### 4.1.5 Precisely scoped conclusions

Three distinct claims must not be conflated, per explicit instruction for this pass:

1. **Established mathematical finding (independent of either document's authorship, and
   independent of the Lean proof).** Under the coordinate relationships both primary
   sources state (`ε'_u=F·x'`, `ε'_{x,d}=F·x''`) and the same-direction (U→D) forward
   Brown-Conrady interpretation both sources use for this comparison, the coefficient
   scaling `q=p/F` is what the algebra requires; `q=p/F²` produces pixel outputs that
   disagree with OpenCV's forward model whenever `F≠1` and tangential distortion is
   nonzero (§4.1.3). This is a statement about the mathematics of the stated model, true
   regardless of which document, if either, is "correct" by the standards of the
   OpenTrackIO ecosystem.
2. **Published-document finding.** The conversion paper's own worked tangential
   derivation (p.3: `p1x'y' = q1ε'_{x,u}ε'_{y,u}`) is **internally inconsistent with its
   own stated coordinate-scaling equations** (p.2: `ε'_{x,d}=F·x''`), under the
   interpretation that both the paper's radial derivation and tangential derivation are
   meant to establish the same kind of coordinate-conjugacy relationship (which the
   paper's own radial derivation does correctly). This is a demonstrated inconsistency
   *under the stated interpretation* of the document's two halves read together — it is
   not a claim that the OpenTrackIO standard as a whole, or OpenLensIO's native
   distortion model (`U`, Eq.16-17), contains an error; those are not in question here.
3. **Still unresolved — not addressed by any of the above:**
   - Whether the paper's authors intended an undocumented convention for `q1,q2` not
     captured by the three-page derivation, for reasons this audit cannot see from the
     document alone.
   - Whether any production system implements `q=p/F²`, `q=p/F`, or neither — checked
     directly against two reference implementations and found that **neither implements
     this conversion at all** (§4.1.4), so this cannot currently be settled by
     implementation survey.
   - **How the U→D conversion this section analyzes relates to OpenLensIO's native D→U
     model.** This is explicitly **not resolved** by this section and should not be read
     as resolved: §4.1.1 establishes that the *comparison performed here* (OpenCV's
     forward map vs. the paper's same-shape `l,q` forward map) is a same-direction,
     coordinate-conjugacy comparison, free of forward/inverse confusion *as a comparison*.
     It says nothing about whether coefficients produced this way, when consumed by a
     real implementation applying OpenLensIO's *native* `U` (the D→U function, Eq.16-17,
     using a separate mm-unit coefficient set never computed by this conversion), would
     produce correct undistortion. Same-direction coordinate conjugacy and native
     inverse-model interoperability are different mathematical obligations, and
     establishing the first does not discharge the second (SQ-CV-07, still fully open,
     pending maintainer response as of this audit).

Resolving items under (3) requires either an erratum/clarification from the paper's
authors (outreach already sent, response pending as of this audit — see
`docs/specification-questions.md` SQ-CV-06/07) or a formal bridge theorem between the
U→D coordinate-conjugacy result and OpenLensIO's native D→U undistortion function — see
the end-of-audit note on what such a theorem would need to state.

---

## 5. Suspected overclaims and counterexamples

### 5.1 "40 mutation-test theorems" — verified miscount, repeated in 7 documents

```sh
grep -cE "^(theorem|lemma|private theorem|private lemma)" opencv_opentrackio_proofs/MutationTests.lean
# → 34
```

All 34 declarations enumerated and confirmed to be `theorem` (none `private`); full list
in the command transcript (lines 23-549 of `MutationTests.lean`). "40 mutation-test
theorems" / "40 explicit mutation tests" appears as load-bearing anti-vacuity evidence in:

- `README.md:57`
- `docs/specification-questions.md:157`
- `docs/maps/system-assurance-map.md:31`
- `docs/maps/correctness-assurance.md:81`
- `docs/maps/evidence-matrix.md:66,181`
- `docs/maps/property-register.md:75`
- `docs/maps/assurance-case.md:103`
- `docs/opentrackio-proof-summary.md:507`

An untracked, uncommitted `opencv_opentrackio_proofs/MutationTestsY.lean` (y-axis mutation
tests, work in progress, not part of the repository's committed/documented state) adds 5
more declarations — even including it, the total is 39, still short of 40, and it is not
part of what any of the eight documents above were describing when written (they predate
or are independent of the y-axis work).

**This is a genuine, repeated documentation-accuracy defect**, not a proof defect — the
34 theorems that do exist are real, sound, and do serve the stated anti-vacuity purpose
(each tests a specific wrong-formula variant and shows it degenerate or inconsistent with
the full-polynomial identity, confirmed by direct reading of a representative sample:
`wrong_l1_power_F4_forces_power_degeneracy`/`_inconsistent`,
`wrong_q2_swapped_p1_forces_equal_coefficients`/`_inconsistent`, etc., each following the
same disciplined two-theorem pattern — not vacuous, not trivially true). But a reader
relying on any of the seven public-facing documents' stated count as evidence of
discrimination coverage is relying on a number that does not match the code.

**Required action:** either add 6 more mutation-test theorems to reach 40 (if 40 was the
original target and some were lost/renamed), or correct the count to 34 in all seven
locations. Given the number is cited as *evidence quantity* (not an arbitrary round
number), the correction should be made promptly — it is easy to verify and easy to fix.

### 5.2 SQ-CV-06 tangential conversion — see §4.1 (confirmed internal inconsistency under the stated interpretation, not a new repository overclaim; the repository's own framing of this as "open" — pending the OpenTrackIO ecosystem's resolution, not pending further mathematical analysis — remains accurate and appropriately hedged; see §4.1.5 for the precise three-way scoping of what is and is not established)

### 5.3 No other P0/P1-severity overclaims found in the headline theorem statements themselves

Checked specifically for: existential-where-uniqueness-expected, conditional-where-total-
expected, bounded/sampled-where-general-expected patterns (per task brief) — not found.
`opencv_openlensio_full_pipeline_pixel_iff` is a genuine universally-quantified ↔, not
restricted to exceptional numeric cases (the ↔ itself is proved for all `x1..p2, l1..q2,
fx,cx,ws,w,F,ΔPx` satisfying the stated hypotheses, not for a finite sample).
`undistortPoint_injective_pure_radial` is genuinely global (all `ε₁,ε₂ : SensorPoint`), not
on-circle-restricted — the on-circle restriction is a *separate, more general* theorem
(`undistortPoint_injective_zero_tangential`) that the pure-radial theorem is built *on top
of*, not a weakening disguised as strengthening. `D_exists_unique_preimage` is local (on a
buffer disk, under a sufficient contraction condition) and is disclosed as local, not
claimed global.

---

## 6. Hypotheses requiring elimination, weakening, or constructive discharge

| Hypothesis | Theorem | Current status | Recommended action |
|---|---|---|---|
| `hden : ∀x'y', denom ≠ 0` | `opencv_openlensio_full_pipeline_pixel_iff`/`_corrected`/`_sufficiency` | Free, opaque, disclosed (SQ-OL-01/SQ-CV-02, open) | Wire in `radialTerm_pos`/`radialTerm_ne_zero`-style constructive discharge (already exists in `InjectivityModel.lean:184-199` for a related but not identical predicate) under explicit coefficient sign/bound conditions, as done for `hScaleInj` in `radialScale_hScaleInj` |
| `hp : p1≠0 ∨ p2≠0` | `opencv_openlensio_full_pipeline_pixel_iff` | Genuine restriction, disclosed in limitations.md but not inline in README's one-sentence summary | Add the caveat inline in `README.md:43` alongside the headline sentence, not only in the linked "Claim scope" paragraph |
| `(_ : WellFormedSampleJson j)` | `wellFormed_normalize_eq_encode`, `normalization_under_wellFormed` | **Unused** — confirmed by proof inspection | Remove, or document why it is retained despite being redundant (§3.5) |
| `hScaleInj` | `undistortPoint_injective_pure_radial` | Already constructively dischargeable via `radialScale_hScaleInj` under sign-separation conditions | No action required — this is the model other free hypotheses in this repository should follow |
| `hcontract : |t|·L θ R < 1` | `D_exists_unique_preimage` et al. | Disclosed sufficient-not-necessary throughout | No action required for this pass; genuinely open whether a necessity result is attainable, correctly left open |

---

## 7. Prioritized remediation backlog

1. **P0.** Fix `lakefile.toml:3`'s `defaultTargets` to include all 63 `lean_lib` targets
   (or restructure to a small number of umbrella `lean_lib`s with exhaustive `globs`), so
   that `lake build` — the command the README documents and any CI presumably runs —
   actually type-checks every headline theorem. Update `README.md:208`'s expected job
   count. Verify whether any existing CI configuration already passes explicit target
   names (if so, this is "only" a local-dev/README trust gap; if not, CI has never
   verified the headline theorems either).
2. **P1.** Correct "40 mutation-test theorems" to "34" (or add 6 more) across all seven
   citing documents (§5.1).
3. **P1.** Remove or justify the unused `WellFormedSampleJson j` hypothesis in
   `wellFormed_normalize_eq_encode` and `normalization_under_wellFormed`
   (`NormalizationTheorems.lean:55-64`); correct `README.md:92-93`'s framing accordingly.
4. **P1.** Add a one-line trust-model note to `docs/limitations.md`'s parser section
   disclosing that `encodeSample_roundtrip`, `sampleNormalize_idempotent`, and
   `normalization_under_wellFormed` depend on `native_decide` (compiler/FFI trust), not
   only the kernel-checked axioms the rest of the repository relies on.
5. **P2 (noted, not detailed here — out of P0/P1 scope).** Fix the `PipelineEquivalence.lean`
   compatibility re-export to also import `Pipeline.PixelIffCorrected` (§2.2); inline the
   `hp` caveat into `README.md:43`'s headline sentence (§3.1.1).
6. **Not a remediation item — a process item.** Continue tracking SQ-CV-06/SQ-CV-07
   maintainer outreach (sent 2026-08-15 to James Uren, Mo-Sys); this audit's §4.1
   independently strengthens the case for SQ-CV-06 but does not close it.

---

## 8. Findings that remain unverified

- **Whether the SMPTE RIS paper's authors intended `q=p/F²` for a reason not captured by
  the three-page PDF reviewed here** (e.g., a downstream consumption convention that
  would make the published formula correct despite the dimensional mismatch identified in
  §4.1). Not resolvable from the document alone; requires the pending maintainer response.
- **Whether real OpenTrackIO producers/consumers currently implement `q=p/F²`, `q=p/F`,
  neither, or treat `distortion.model` direction as advisory** — SQ-CV-07, genuinely open,
  outside what any Lean proof or document inspection can resolve without external
  implementation survey.
- **Whether any CI configuration exists and, if so, whether it already passes explicit
  Lake target names** — not found in the repository root (no `.github/workflows/` or
  equivalent was located in this pass; this audit did not exhaustively search for CI
  configuration outside the standard locations, so its absence is reported as "not found,"
  not "confirmed absent").
- **`docs/OpenLensIO_v1-0-1.pdf`** was read in full during the hostile-review pass
  (§4.1), correcting the original pass's "not deep-read" note. A by-product check: SQ-OL-02's
  claimed Eq.8/Eq.15 overscan asymmetry is directly visible in the text as read — Eq.8
  (`ε_Ω=(1/Ω)U(ε_d-ΔC-ΔP)`) re-adds neither `ΔC` nor `ΔP` after applying `U`, while Eq.15
  (`ε'_Ω'=(1/Ω')(U(ε_d-ΔC-ΔP)+ΔC)`) re-adds `ΔC` but not `ΔP` — confirming the repository's
  characterization of an asymmetry, though *why* the two forms differ is not explained in
  the document and remains open (SQ-OL-02, status: deferred, unchanged by this audit).
  SQ-OL-01's denominator-nonzero silence was not independently re-checked beyond confirming
  the `R` formula (Eq.17) itself states no domain restriction; a full audit of SQ-OL-01/02
  remains out of scope for this P0/P1 pass, which was focused on the tangential-conversion
  finding in §4.1.
- **The "~100 public theorems" aggregate count** in `docs/opentrackio-proof-summary.md:7`
  was not independently re-verified against a precise "public" (non-`private`,
  non-helper) theorem census; a blunt `grep -c "^theorem |^lemma "` across the whole repo
  returns 185, but that figure includes private/helper lemmas and uncommitted
  y-axis-in-progress files, so it is not a like-for-like comparison and is not reported as
  a confirmed discrepancy (unlike the 34-vs-40 mutation-test count, which was verified on
  a clean, unambiguous, single-file, single-declaration-kind count).
