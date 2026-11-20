# Proof Plan — inverse-conjugacy-bridge

## Subgoal ledger

1. `OpenTrackIOModel.lean`: `distortXOTI`, `distortYOTI`, `distortPointOTI` — pure
   definitions, same shape as `distortXCV`/`distortYCV`/`distortPointCV`
   (`OpenCVModel.lean:41-83`), `l1..l6,q1,q2` in place of `k1..k6,p1,p2`. No proof
   obligation beyond type-checking.
2. `PixelIffCorrectedY.lean`: `opencv_openlensio_full_pipeline_pixel_corrected_y` — new
   proof obligation. Opening move: `intro x' y'`, mirroring
   `opencv_openlensio_full_pipeline_pixel_corrected`'s proof shape exactly (same `h_num`,
   `h_den` local haves — symmetric in x',y', so re-derivable verbatim — then
   `rw [h_num, h_den, hq1, hq2, hΔPy, hF_eq]; field_simp [...]; ring`). Goal shape:
   equality of two rational expressions in `x',y'` after substitution — a `field_simp`+
   `ring` goal, same family as the existing x-proof, which is the direct evidence this
   closes the same way. Hard step: none beyond what the existing x-proof already
   demonstrates is tractable with this tactic sequence (no new mathematical content — only
   the p1/p2 role swap, already a proven-safe transformation per `DistortionConversion.lean`
   vs `OpenCVModel.lean`'s own symmetric x/y treatment). Automation budget: `field_simp`
   once (denominators: `h`, `h_shader`, `fy`, and the CV/OTI rational denominators,
   all `≠0` by hypothesis/derivation — listed before calling, per the Algebra Tripwire
   gate) + `ring` to close.
3. New file (name TBD at write time, likely `ForwardConjugacy.lean`): the 2D
   `SensorPoint`-level conjugacy. Goal shape: `SensorPoint` equality, opening move
   `SensorPoint.ext` splitting into x/y real equalities, each closed by *unwrapping* the
   already-proven pixel theorems (x: existing `opencv_openlensio_full_pipeline_pixel_corrected`;
   y: step 2's new theorem) — subtract the shared `+cx`/`+cy` additive term (via
   `principal_offset_cancels`-style algebra, reusable as-is for y with renamed arguments)
   and divide through by `fx`/`fy` (nonzero, derived exactly as the existing proof already
   derives `hfx`/`hfy`) using `hF_eq`. Requires bridging `distortXCV`/`distortXOTI`
   (`SensorPoint`/`sensorRadius`-based) to the raw-`x'^2+y'^2` form the pixel theorems use,
   via `Real.sq_sqrt` — a known, low-risk rewrite (same technique already used in
   `InjectivityModel.lean:151-154`). Hard step: correctly tracking that a GENUINE single-`F`
   2D statement requires both `F=(w/ws)*fx` and `F=(h/h_shader)*fy` as hypotheses
   simultaneously (the x and y pixel theorems otherwise reference two independently-named
   focal-length relations) — stated explicitly as two named hypotheses, not derived from
   `single_focal_length_compatibility` (out of scope; simpler to state directly).
4. New top-level file (no project imports): abstract inverse-conjugacy lemma over
   `Set.InjOn`/`Set.BijOn`. Pure Mathlib. Goal shape: existence/uniqueness-flavored
   statement about `Set.BijOn.equiv`-style inverses or an explicit `Set.LeftInvOn`/
   `Set.RightInvOn` pair. Opening move: `intro`/`apply` on the relevant `Set.BijOn`
   constructor; closing via function composition identities, standard Mathlib lemmas
   (`Set.BijOn.comp`, `Equiv.symm`, or manual `Function.LeftInverse`/`RightInverse`
   composition facts) — theorem lookup (`exact?`) expected to find the needed composition
   lemmas rather than hand-deriving.
5. Specialization file: apply (4) to (3)'s conjugacy fact plus an explicit, undischarged
   `Set.InjOn`/`Set.BijOn` hypothesis on `distortPointCV`. No new proof content beyond
   instantiation.

## Automation budget
`field_simp`/`ring` for steps 2-3 (algebra, same family already proven tractable in this
file tree); `exact?`/direct Mathlib lemma application for step 4 (standard set-theoretic
function facts, not project-specific algebra).

## Reusable technique
Pixel-level ↔ distortion-level "unwrap by subtracting the shared offset and dividing by
the nonzero focal length" (step 3) is a new, project-reusable technique — record in
`proof-review.md` if used successfully, since it would also let a future y-corrected or
x-published/y-published 2D theorem be derived the same way without new tangential algebra.
