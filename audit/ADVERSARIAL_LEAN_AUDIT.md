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

3. **(P1 — independently confirmed specification defect, not just repeated)** Direct
   inspection of the primary source (`docs/OpenCV_to_OpenTrackIO.pdf`, the SMPTE RIS
   conversion paper itself, not merely the repository's paraphrase of it) shows the
   paper's own worked tangential-distortion derivation (p.3) is dimensionally inconsistent
   with the coordinate relation the same paper states two paragraphs earlier (p.2,
   `ε'_{x,d} = F·x''`). This independently corroborates — via a fresh re-derivation from
   the primary source, not by trusting the repository's framing of it — the repository's
   own SQ-CV-06 finding that the published tangential conversion `q₁ = p₁/F²` is likely a
   paper-level defect and `q₁ = p₁/F` is dimensionally consistent with the paper's own
   coordinate definitions. See §4 and §5.2. This remains open pending the maintainers'
   response (sent 2026-08-15, per `docs/specification-questions.md` SQ-CV-06).

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
(OpenLensIO) lens calibration parameters," corrected 2025-09-02) and
`docs/OpenLensIO_v1-0-1.pdf` (present but not deep-read for this pass — out of P0/P1 scope
except where it bears on SQ-CV-06/07 below).

| Claim | Normative source (equation) | Lean definition | Units/convention | Direction | Hidden assumptions | Status |
|---|---|---|---|---|---|---|
| Radial conversion `l1=k1/F², l3=k2/F⁴, l5=k3/F⁶` (numerator); `l2=k4/F², l4=k5/F⁴, l6=k6/F⁶` (denominator) | PDF p.2-3, "Comparing individual components... $k_1 r^2 = l_1 r_u^2 = l_1 F^2 r^2$" | `DistortionConversion.lean:57-66` (`radial_distortion_conversion`, generic over `n`), instantiated at n=1,2,3 | OpenCV normalized coords `(x',y')` vs OpenTrackIO screen coords `(ε'_u = F·x')` | U→D (both sides describe the undistorted→distorted multiplicative factor) | None found — transcription matches the PDF verbatim, including the structure of the derivation (term-by-term match after substituting `r_u = F·r`) | **Established** — verified against primary source, not just repository paraphrase |
| Tangential conversion `q1=p1/F², q2=p2/F²` (as-published) | PDF p.3, "$p_1 x' y' = q_1 \epsilon'_{x,u}\epsilon'_{y,u} = q_1 F x' F y' \Rightarrow q_1 = p_1/F^2$" | `DistortionConversion.lean` `tangential_q1_conversion`/`tangential_q2_conversion`; consumed by `PixelIff.lean:36` (`hq1,hq2`) | same | U→D | **The paper's own term-by-term matching treats the additive tangential displacement the same way it treats the multiplicative radial factor — see dimensional-analysis finding below** | **Disputed — independently re-derived, see below** |
| Focal length / principal point `F = (w/ws)·fx`, `ΔPx = (w/ws)·(cx − ws/2)` | PDF p.2, "Focal length and projection offset parameters" | `PixelIff.lean:33,37` (`hF_eq`, `hΔPx`) | pixel ↔ screen-shader units via `w/ws` ratio | — | None found — transcription matches verbatim, including the corrected `−w_shader/2` term the paper itself flags as a prior-version bug (PDF p.2, "Note that in a previous version... was missing") | **Established** |
| Corrected tangential `q1=p1/F, q2=p2/F` | Not in the PDF — repository's own re-derivation (`docs/specification-questions.md` SQ-CV-06) | `DistortionConversionCorrected.lean`; consumed by `PixelIffCorrected.lean:78` | same | U→D | Repository-internal derivation, not yet confirmed by the paper's authors | **Open — maintainer response pending (sent 2026-08-15)**; independently supported by this audit's dimensional analysis (below), not yet independently confirmed by a reference implementation or the paper's authors |
| Pipeline theorems compare U→D formula shape on both sides | PDF defines `ε'_{x,d} = F·x''` (p.2) — i.e. relates *distorted* coordinates, which is what the Lean pipeline theorems reproduce | `Pipeline/PixelIff.lean:42-57`, `Pipeline/PixelIffCorrected.lean:83-100` | — | **Both sides U→D** — this is what the PDF's own equations describe | Separately, the OpenTrackIO *JSON schema*'s `distortion.model` field defaults to `"Brown-Conrady D-U"` (opposite direction) when omitted — this is a schema-level question, not a question about whether the Lean theorems faithfully formalize the PDF's U→D equations (they do) | **Established that the Lean theorems match the PDF's U→D equations; separately open whether a real producer/consumer is expected to tag `model="Brown-Conrady U-D"` for these coefficients to apply correctly — SQ-CV-07, maintainer response pending** |

### 4.1 Independent dimensional analysis: is `q=p/F²` or `q=p/F` consistent with the paper's own definitions?

The task brief specifically asks for this to be checked by direct symbolic substitution
rather than assumed. Worked below, using only the PDF's own stated definitions (not the
repository's framing of them).

The PDF defines (p.2): `ε'_{x,u} = F·x'` (undistorted screen coordinate) and
`ε'_{x,d} = F·x''` (distorted screen coordinate), where `x''` is OpenCV's distorted
normalized coordinate. OpenCV's `x''` decomposes as a **multiplicative radial** part plus
an **additive tangential** part:

```
x'' = R_cv(r)·x' + T_cv(x',y')      where T_cv(x',y') = 2p1·x'y' + p2·(r²+2x'²)
```

and OpenTrackIO's `ε'_{x,d}` decomposes the same way in its own coordinates:

```
ε'_{x,d} = R_oti(r_u)·ε'_{x,u} + T_oti(ε'_{x,u}, ε'_{y,u})
         = R_oti(r_u)·F·x' + T_oti(F·x', F·y')
```

For `ε'_{x,d} = F·x''` (the PDF's own stated relation) to hold **for every lens**, i.e.
for arbitrary independent `R_cv` and `T_cv` pieces (radial and tangential coefficients are
independent parameters), it must hold termwise:

```
R_oti(r_u)·F·x'            =  F·R_cv(r)·x'      ⟹  R_oti(r_u) = R_cv(r)   (*)
T_oti(F·x', F·y')          =  F·T_cv(x',y')                                (**)
```

`(*)` is exactly what the PDF derives for the radial coefficients (p.2-3): the paper
substitutes `r_u = F·r` into `R_oti` and matches it directly to `R_cv(r)` term-by-term
(`k1·r² = l1·r_u²`, no extra `F` factor on either side beyond what `r_u=F·r` already
contributes) — correctly consistent with `(*)`, since `R_oti` is dimensionless and the
single explicit `F` in `ε'_{x,u}=F·x'` already accounts for everything.

`(**)` requires `T_oti(F·x',F·y') = F·T_cv(x',y')` — **one explicit factor of `F` beyond
what the coordinate substitution contributes**, because `T` is an *additive* displacement,
not a multiplicative scale factor: substituting `r_u=F·r`-style arguments into `T_oti`
does not, by itself, produce the needed overall factor of `F` the way it does for `R_oti`.

Substituting `T_oti(ε_x,ε_y) = 2q1·ε_xε_y + q2(ε_x²+ε_y²+2ε_x²)` with `ε_x=Fx',ε_y=Fy'`:

```
T_oti(Fx',Fy') = F²·(2q1·x'y' + q2(x'²+y'²+2x'²)) = F²·T_cv^{q→p slot}(x',y')
```

So `(**)` becomes `F²·T_cv^{q}(x',y') = F·T_cv^{p}(x',y')`, and matching the linearly
independent monomials `x'y'` and `(r²+2x'²)` gives `F²q1 = F·p1` and `F²q2 = F·p2`, i.e.

```
q1 = p1/F,   q2 = p2/F
```

**— the repository's "corrected" formula, not the paper's own published `q=p/F²`.**

The PDF's own worked derivation (p.3) instead writes `p1·x'·y' = q1·ε'_{x,u}·ε'_{y,u}`
directly — i.e. it imposes `T_oti(Fx',Fy') = T_cv(x',y')` (zero explicit extra factor of
`F`, matching `(**)` with the right-hand side missing its `F`), which gives `q=p/F²`. This
is dimensionally inconsistent with the paper's own `ε'_{x,d}=F·x''` relation once `x''` is
correctly decomposed into its (multiplicative) radial and (additive) tangential parts: the
paper appears to have applied the *same* "substitute-and-match" procedure it correctly
used for the radial terms to the tangential terms as well, without accounting for the fact
that an additive displacement term needs its own independent factor of `F` to remain
consistent with the overall `ε'_d = F·x''` scaling, whereas the multiplicative radial
factor does not (the `F` it needs is already supplied by the coordinate substitution
itself).

**This audit independently confirms, via direct substitution into the PDF's own equations
— not by trusting the repository's restatement of its own claim — that the published
`q=p/F²` formula is dimensionally inconsistent with the paper's own `ε'_{x,d}=F·x''`
definition, and that `q=p/F` is what that definition requires.** This strengthens
SQ-CV-06 from "the repository's own internal re-derivation disagrees with the paper" to
"an independent re-derivation from the primary source, performed fresh for this audit,
agrees with the repository's re-derivation and disagrees with the paper's worked
example."

**What this does NOT establish:** (a) whether the paper's authors intended something not
captured in this three-page derivation (e.g. a different convention for how `q1,q2` are
meant to be *consumed* downstream that would make `p/F²` correct in context despite this
analysis); (b) which of `q=p/F²` or `q=p/F` real OpenTrackIO producers/consumers currently
implement or expect, if either; (c) the separate, still-fully-open SQ-CV-07 question of
whether either convention, once resolved, bears on the D-U vs. U-D direction question at
all. These remain genuinely unverified and are not resolved by this audit — resolving
them requires either an erratum from the paper's authors (outreach already sent, response
pending as of this audit) or an independent reference-implementation comparison, as the
repository itself states (`docs/specification-questions.md:165-174`).

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

### 5.2 SQ-CV-06 tangential conversion — see §4.1 (independently confirmed, not a new overclaim; the repository's own framing of this as "open" is accurate and appropriately hedged)

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
- **`docs/OpenLensIO_v1-0-1.pdf`** was located but not deep-read for this pass (out of
  P0/P1 scope beyond its bearing on SQ-CV-06/07 above); the overscan asymmetry (SQ-OL-02)
  and denominator-nonzero silence (SQ-OL-01) claims about this document were taken from
  the repository's own citation, not independently re-verified against the PDF text in
  this pass.
- **The "~100 public theorems" aggregate count** in `docs/opentrackio-proof-summary.md:7`
  was not independently re-verified against a precise "public" (non-`private`,
  non-helper) theorem census; a blunt `grep -c "^theorem |^lemma "` across the whole repo
  returns 185, but that figure includes private/helper lemmas and uncommitted
  y-axis-in-progress files, so it is not a like-for-like comparison and is not reported as
  a confirmed discrepancy (unlike the 34-vs-40 mutation-test count, which was verified on
  a clean, unambiguous, single-file, single-declaration-kind count).
