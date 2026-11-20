# Proof Capsule — inverse-conjugacy-bridge

## Task size
Large (5 steps, 2 new files, 2 genuinely new proof obligations).

## Context
Follow-up to SQ-CV-07 (`docs/specification-questions.md`), per
`audit/DISTORTION_DIRECTION_INTEROPERABILITY.md` Candidate 2. Goal: the smallest
meaningful bridge from the already-proved same-direction forward conjugacy
(`opencv_openlensio_full_pipeline_pixel_corrected`) to a genuine statement about
inverses — without claiming anything about OpenLensIO's native `U`, without a finite
inverse-coefficient formula, and without numerical-inversion machinery.

## Declarations to add (exact statements fixed before any tactic work)

1. `distortXOTI`, `distortYOTI`, `distortPointOTI` — new file
   `opencv_opentrackio_proofs/Pipeline/OpenTrackIOModel.lean`. Same formula shape as
   `distortXCV`/`distortYCV`/`distortPointCV` (`OpenCVModel.lean:41-83`), parameterized by
   `l1 l2 l3 l4 l5 l6 q1 q2 : ℝ` instead of `k1..k6 p1 p2`. Definitional, not proved.

2. `distortXCV_eq_bracket` / a direct `unfold+ring`-style bridging step: connects
   `distortXCV k1..k6 p1 p2 ⟨x',y'⟩ h` to the literal bracketed real-number expression
   `opencv_openlensio_full_pipeline_pixel_corrected` already states, via
   `Real.sq_sqrt (show (0:ℝ) ≤ x'^2+y'^2 from ...)`. Same bridging step needed for the OTI
   side against `distortXOTI`.

3. **New proof obligation**: `opencv_openlensio_full_pipeline_pixel_corrected_y` (or
   equivalent name) — the Y-axis analogue of the existing X-axis
   `opencv_openlensio_full_pipeline_pixel_corrected` (`PixelIffCorrected.lean:71-132`),
   under the corrected `q=p/F` scaling. Mirrors `PixelSufficiencyY.lean`'s proof technique
   (y-axis, as-published family) and `DistortionConversionCorrected.lean`'s per-term
   corrected-scaling lemmas (`whole_tangential_field_2d_iff_physical`, already covers both
   x,y tangential conjuncts at the coefficient level, lines 115-138). New helper lemmas
   follow the `PixelIffHelpersY.lean` pattern (p1↔p2 role swap).

4. **New 2D theorem** (Step 3): a `SensorPoint`-level equality
   `distortPointOTI l1..l6 q1 q2 (S_F ⟨x',y'⟩) hden' = S_F (distortPointCV k1..k6 p1 p2 ⟨x',y'⟩ hden)`
   where `S_F ⟨x,y⟩ := ⟨F*x, F*y⟩`, proved via `SensorPoint.ext`, invoking (2) for both
   components, (3) for the y-component pixel-level fact reduced to the raw distortion-level
   fact, and the existing x-component theorem for the x half. Must not take the desired
   equality as a hypothesis.

5. **New abstract lemma** (Step 4): standalone function-conjugacy-of-inverses fact, no
   project-specific imports, stated via `Set.InjOn`/`Set.BijOn`/explicit two-sided partial
   inverse — not global bijectivity.

6. **New specialized theorem** (Step 5): applies (5) to (4), with the CV-side
   injectivity/existence condition as an explicit, undischarged, named hypothesis (none
   exists in this repository for `distortPointCV` — confirmed: `InjectivityModel.lean`'s
   injectivity results are for `undistortPoint`/`RadialCoefficients`, a different type).

## Hard constraints
- No edit to any existing committed theorem statement or proof.
- No `sorry`/`admit`/custom `axiom`/`native_decide`/`unsafe`/`partial`.
- No toy model; actual `distortXCV`/`distortYCV` and actual corrected `l=k/F^(2n)`,
  `q=p/F` relations throughout.
- `Function.invFun` (if used) must have its outside-domain junk behavior stated explicitly,
  never relied on silently.
- Specialized theorem (6) must not claim anything about OpenLensIO's native `U`, a finite
  inverse-coefficient set, numerical computation, or SQ-CV-07 resolution.

## Plain-English translation
"The map from OpenCV's normalized plane to OpenTrackIO's screen plane, built from the
already-proved coordinate-conjugate forward distortion (both x and y), has an inverse
exactly where OpenCV's own forward map has one — and that inverse is given by the same
coordinate conjugation, not by inverting OpenTrackIO's coefficients independently." This
matches the requested claim: it is a conjugacy-of-inverses fact about the two *already-
proved-equal* forward maps, not a claim about any third function (OpenLensIO's native `U`)
or about how to compute the inverse in practice.
