# Proof Review — inverse-conjugacy-bridge

## A. Scope

Theorem inventory (exact, via `grep -n "^theorem\|^noncomputable def\|^def " <files>`):
- `opencv_opentrackio_proofs/Pipeline/OpenTrackIOModel.lean`: `distortXOTI`, `distortYOTI`,
  `distortPointOTI` (definitions, no proof obligation).
- `opencv_opentrackio_proofs/Pipeline/PixelIffCorrectedY.lean`: `opencv_openlensio_full_pipeline_pixel_corrected_y`.
- `opencv_opentrackio_proofs/Pipeline/ForwardConjugacy.lean`: `ScreenScale` (definition),
  `opencv_openlensio_forward_point_corrected`.
- `opencv_opentrackio_proofs/InverseConjugacy.lean`: `conjugate_invOn`.
- `opencv_opentrackio_proofs/Pipeline/InverseConjugacyApplication.lean`:
  `denom_sensorRadius_ne_zero`, `CVmap`, `OTImap` (definitions), `screenScaleEquiv`
  (definition), `opencv_openlensio_inverse_conjugate`.
- `opencv_opentrackio_proofs/Pipeline/InverseConjugacyExample.lean`: one `example` (no
  name — not a theorem to be cited elsewhere, a verification artifact only).

Review type: exhaustive, theorem-by-theorem, of these 6 new files only — no re-audit of
any existing file (none was modified; confirmed via `git diff --stat` returning empty for
every file named off-limits in the task).

## B. Kernel Status

Command: `lake build Pipeline.OpenTrackIOModel Pipeline.PixelIffCorrectedY
Pipeline.ForwardConjugacy InverseConjugacy Pipeline.InverseConjugacyApplication
Pipeline.InverseConjugacyExample` — all succeed, most recent run: see
`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md` for the consolidated build transcript.

`#print axioms` on every named theorem/def with a proof obligation: all depend only on
`propext, Classical.choice, Quot.sound`; `conjugate_invOn` depends only on `Quot.sound`
(no real-number reasoning in its proof). No `sorry`, `admit`, custom `axiom`,
`native_decide`, `unsafe`, or `partial` anywhere (grep, zero matches).

## C. Semantic Review

### Does each theorem match its intended claim?

- `opencv_openlensio_full_pipeline_pixel_corrected_y`: yes — the y-axis mirror of the
  existing x-axis corrected theorem, same hypothesis shape (p1↔p2 role swap), same
  unconditional conclusion. Not a restatement of the x-theorem; a genuinely new proof
  obligation (confirmed no `_corrected_y` declaration existed anywhere before this slice).
- `opencv_openlensio_forward_point_corrected`: yes, and this is the slice's main
  correctness-sensitive claim — it is a DISTORTION-level (not pixel-level) 2D conjugacy,
  and it is derived FROM the pixel-level theorems (both x and y), not merely restated in
  `SensorPoint` notation. Verified: the proof instantiates
  `opencv_openlensio_full_pipeline_pixel_corrected`/`_corrected_y` and algebraically
  unwraps the shared `cx`/`cy` offset and `fx`/`fy` scale via `principal_offset_cancels`-
  style identities (reproduced locally as `hoff_x`/`hoff_y`, not copy-imported, since they
  are one-line `field_simp`+`ring` facts) and `hscale_x`/`hscale_y`, then cancels the
  nonzero `ws/w`/`h_shader/h` factor via `mul_left_cancel₀`. No step assumes the
  conclusion.
- `conjugate_invOn`: yes — a standard, correctly-hypothesized partial-inverse conjugacy
  fact. Hypotheses are `Set.InvOn` on explicit sets, not global bijectivity.
- `opencv_openlensio_inverse_conjugate`: yes, and its doc-comment explicitly lists five
  things it does NOT claim (native `U` equality, finite inverse coefficients, numerical
  correctness, float certification, SQ-CV-07 resolution) — reviewed against the actual
  proof body and confirmed none of those five appear anywhere in the statement or proof.

### Is any theorem vacuous?

No. The concrete instantiation (`InverseConjugacyExample.lean`) exhibits a non-identity,
nonzero-coefficient (`k1=1,p1=1`), nonzero-`F` (`F=2≠1`) satisfying assignment for every
hypothesis of `opencv_openlensio_inverse_conjugate`, including `hCVInv` (via a singleton-
set witness) — the hypothesis set is not unsatisfiable, and the theorem is not vacuously
true only because no assignment exists.

### Are the hypotheses necessary / correctly classified?

- `hden`, `hdenOTI`: free, universally-quantified domain conditions — same pattern as
  every existing pipeline theorem in this repository; not newly introduced risk.
- `hF_eq_x`, `hF_eq_y` (two separate focal-length relations, both constrained to the SAME
  `F`): necessary for a genuine single-scale 2D statement — without both, the x and y
  pixel theorems would only license two DIFFERENT scale factors, not one `ScreenScale F`
  applicable to both components at once. Not derived from `single_focal_length_compatibility`
  (out of scope per the task) — stated directly as two hypotheses instead, which is
  honest and not weaker (a real single-focal-length camera satisfies both by construction).
- `hCVInv : Set.InvOn cv' (CVmap ...) A B`: **the one substantive, undischarged hypothesis
  in the entire slice.** Confirmed no existing theorem in this repository discharges it —
  `InjectivityModel.lean`'s results are for `undistortPoint`/`RadialCoefficients`, a
  different function over a different type, not applicable to `CVmap`/`distortPointCV`
  without a separate bridging argument (not attempted here, and not claimed to be
  attempted). This is reported, not hidden — see the file's own header comment and
  `audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`'s hypothesis inventory.

### Hard step identification

`ForwardConjugacy.lean`'s algebraic unwrapping (pixel-level ↔ distortion-level, via the
shared-offset-cancellation technique) is the hard step of the whole slice — it is the one
piece of genuinely new mathematical content (everything in `InverseConjugacy.lean` is
standard function theory; everything in `InverseConjugacyApplication.lean` beyond that is
plumbing). It was identified in `proof-plan.md` before tactic work began and closed in two
build iterations (one rewrite-ordering fix), not a spiral.

### Anti-pattern scan

No tactic soup (every `have` has a stated role in-file or in `proof-run-log.md`); no
algebra ping-pong (each `field_simp`/`ring` call closes its goal on first use after the
one rewrite-ordering fix in Step 3); no annotation desperation (no `[simp]`/`[grind]`
added anywhere); no automation hiding a hard step (the hard step — the offset/scale
unwrapping — is spelled out as explicit named `have`s, not buried in a single opaque
`simp`/`aesop` call); no runtime-failure-replacing-proof (no `partial`/panic/unchecked
indexing anywhere in the new files).

## D. Required Action Split

- Mathematical/proof action: none — all 5 steps complete and kernel-checked.
- Documentation action: covered by `audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`.
- Process-evidence action: none outstanding — build commands, axiom results, and forbidden-
  construct scan are all recorded with exact commands in `proof-run-log.md` and the audit
  deliverable, not merely asserted.

## E. Final Classification

**Accepted.** All five requested steps are proved, kernel-checked, free of forbidden
constructs, and depend only on standard axioms. The slice's one genuinely open item
(`hCVInv`) is an intentional, explicitly-flagged scope boundary — the task asked for the
smallest meaningful bridge, not a resolution of `distortPointCV`'s invertibility, and the
proof-capsule/this review both state that boundary plainly rather than discharging it with
an unjustified assumption.
