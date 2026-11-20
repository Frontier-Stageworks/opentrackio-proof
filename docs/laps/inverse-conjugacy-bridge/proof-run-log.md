# Proof Run Log — inverse-conjugacy-bridge

## Entry 1 — initial grounding
Confirmed `opencv_openlensio_full_pipeline_pixel_corrected` does not call `distortXCV`/
`distortYCV` (fully inlined over raw `x',y' : ℝ`); confirmed `distortXCV k1..k6 p1 p2
⟨x',y'⟩ h`, after `Real.sq_sqrt`, is propositionally equal to the bracketed CV expression
that theorem's proof manipulates. Confirmed `SensorPoint` (`CoordinateTypes.lean:26`) is
already reachable from `Pipeline/OpenCVModel.lean`'s existing import chain — no new heavy
dependency. Confirmed no `_corrected_y` file exists anywhere (grep, zero matches).

Entries below are appended as each file is built and checked; see also the Lean build
transcript captured in `audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`.

## Entry 2 — Step 1: Pipeline/OpenTrackIOModel.lean
First attempt: `import OpenCVModel` failed with "unknown module prefix 'OpenCVModel'" —
module is `Pipeline.OpenCVModel` since the file lives under the `Pipeline/` subdirectory
(the srcDir-relative module path includes the subdirectory as a namespace segment).
Classification: missing-theorem-style import-path error (not a tactic/type error).
Fix: `import Pipeline.OpenCVModel`. Rebuilt `lake build Pipeline.OpenTrackIOModel` —
succeeded, 3290 jobs, no warnings. `distortXOTI`, `distortYOTI`, `distortPointOTI`
type-check with the same signature shape as `distortXCV`/`distortYCV`/`distortPointCV`.

## Entry 3 — Step 2: Pipeline/PixelIffCorrectedY.lean
Mirrored `opencv_openlensio_full_pipeline_pixel_corrected`'s proof shape exactly
(h_num/h_den local haves, unchanged since symmetric in x'/y'; tangential substitution via
hq1/hq2 directly; field_simp+ring close). Omitted an hF_pos hypothesis (the x-theorem has
one but its own linter output already flags it unused) — compiled successfully without it,
confirming it is genuinely unnecessary for this proof, not merely unused-but-latent.
`lake build Pipeline.PixelIffCorrectedY` — succeeded first attempt, 3287 jobs, zero new
warnings. No algebra tripwire fired (field_simp called once, ring closed immediately).

## Entry 4 — Step 3: Pipeline/ForwardConjugacy.lean (the 2D conjugacy theorem)
First attempt failed: `simp only [distortXOTI, ScreenScale]` unfolded `ScreenScale F ε` to
the anonymous-constructor literal `{x:=F*ε.x,y:=F*ε.y}` BEFORE the subsequent
`rw [show sensorRadius (ScreenScale F ε)^4 = ...]` ran, so the rw's pattern
`sensorRadius (ScreenScale F ε)` no longer existed in the goal (it had already become
`sensorRadius {x:=F*ε.x,y:=F*ε.y}`, a different term post-unfold). Classification: wrong
rewrite ORDER (not a wrong-direction rewrite) — unfolding ScreenScale too early destroyed
the rewrite target. Fix: split into two simp passes — `simp only [distortXOTI]` (or
`distortYOTI`) first (unfolds the distortion formula but leaves `ScreenScale F ε` opaque,
matching `hr2_oti`'s stated form), THEN the sensorRadius^4/^6 + hr2_oti rewrites, THEN a
second `simp only [ScreenScale]` to resolve the remaining `(ScreenScale F ε).x`/`.y` field
projections. Rebuilt — succeeded, 3294 jobs, no new warnings. One algebra-adjacent fix,
not an algebra-tripwire case (the failure was a rewrite-ordering/unfold-sequencing issue,
classified and fixed on the first retry, not a repeated `field_simp`/`ring` spiral).

The final per-coordinate cancellation (`key`/`key2`/`mul_left_cancel₀`) compiled on the
first attempt with no field_simp/ring spiral — `linarith [hpixel_x, hoff_x]` closed the
linear-rearrangement step treating the two bracket expressions as opaque atoms, and `ring`
closed the pure-associativity `key2` step.

Reusable technique confirmed: "unfold a composed/scaled-point argument's distortion
formula before, not together with, unfolding the scaling function itself, when a
sensorRadius-squared bridging lemma needs to match against the still-opaque scaled point."
Recorded here per the Reusable Technique Check (not promoted to proof-plan.md — single use
so far, not yet confirmed to recur).

## Entry 5 — Steps 4 and 5
Step 4 (InverseConjugacy.lean, abstract `conjugate_invOn`): compiled on first attempt, no
warnings. Used `Set.InvOn`'s `⟨_,_⟩` conjunction structure directly (LeftInvOn component
via `rintro y ⟨a, haA, rfl⟩; simp only [Function.comp_apply]; rw [hconj a,
Equiv.symm_apply_apply, hf'.1 haA]`; RightInvOn/second component symmetric). No theorem
lookup needed beyond `Equiv.symm_apply_apply`, a standard, well-known Mathlib lemma name
(not guessed — used identically to how `InjectivityModel.lean`/other files in this
repository already invoke standard Mathlib Equiv/field lemmas by name).

Step 5 (Pipeline/InverseConjugacyApplication.lean): required bridging `distortPointCV`/
`distortPointOTI`'s dependently-typed domain hypothesis into plain `SensorPoint→SensorPoint`
functions (`CVmap`/`OTImap`, closing over a global `hden`/`hdenOTI` via the new
`denom_sensorRadius_ne_zero` bridging lemma — same `Real.sq_sqrt` technique as Step 3) so
`conjugate_invOn` (stated over plain functions) could apply. Built `screenScaleEquiv F hF :
SensorPoint ≃ SensorPoint` (two-sided inverse `ScreenScale F⁻¹`, proved via `field_simp`
given `hF : F≠0`). Compiled on first attempt, no new warnings. `hCVInv` is taken as an
explicit, named, undischarged hypothesis (`Set.InvOn cv' (CVmap ...) A B`) — no theorem in
this repository discharges it for `distortPointCV`/`CVmap` on any A, B (confirmed: the
existing injectivity results in `InjectivityModel.lean` are for `undistortPoint`, operating
on `RadialCoefficients`/`TangentialCoefficients`, a different type from the raw-ℝ
parameters `CVmap` takes — not applicable here without a separate bridging argument not
attempted in this slice).

## Entry 6 — concrete nontrivial numeric instantiation (Pipeline/InverseConjugacyExample.lean)
Calibration: k1=1 (rest 0), p1=1, p2=0 (nonzero radial AND tangential — not the identity
map), F=2, fx=fy=1, w=2,ws=1,h=2,h_shader=1 (F=(w/ws)*fx=2 ✓, shared across both axes),
cx=cy=0 (ΔPx=ΔPy=-1). Point ε₀=(1,0). Hand-computed (and separately norm_num-verified):
CVmap(1,0)=(2,1); ScreenScale 2 (1,0)=(2,0); OTImap(2,0)=(4,2) = ScreenScale 2 (2,1).
`hCVInv` instantiated on the singleton sets A={(1,0)}, B={(2,1)} with the constant function
cv'=fun _=>(1,0) — a legitimate, non-vacuous (nonzero-coefficient, non-identity-map)
witness that `Set.InvOn cv' (CVmap ...) A B` is satisfiable, not merely that the theorem
type-checks. First attempt had two bugs, both caught by the type-checker immediately (not
silent): (1) the `example` statement's own OTImap argument used `l1=1` instead of the
correct `l1=k1/F²=1/4` — classification: theorem-statement/argument mismatch, not a tactic
failure; fixed by correcting the literal. (2) `ΔPx=ΔPy=0` was passed but the correct values
satisfying `hΔPx`/`hΔPy` are `-1` (arithmetic error in my own setup, not a Lean error) —
caught before the first build attempt by re-deriving by hand once I added the ΔPx/ΔPy
doc-comment. Final proof: `SensorPoint.ext` into two `simp only [...]; norm_num` goals
(switching from a bare `simp [...]` to `simp only [...]` with an explicit lemma list after
the default simp set closed one branch prematurely, leaving `norm_num` with "no goals" —
classification: automation-too-broad, fixed by narrowing the simp set, not by chasing a
tactic spiral; one fix, not a repeated attempt). Builds clean, zero warnings.

## Final status
All 5 steps complete, zero `sorry`, zero forbidden constructs, all new declarations depend
only on `propext, Classical.choice, Quot.sound` (`conjugate_invOn` needs only
`Quot.sound`). No existing committed file's theorem statement or proof was modified
(confirmed via `git diff --stat` on every file the task named as off-limits — empty diff).
Concrete, non-identity, nonzero-coefficient numeric instantiation kernel-checked.
