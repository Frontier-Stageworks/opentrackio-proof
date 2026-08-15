---
name: tangential-conversion-physical-fix-proof-plan
description: Proof plan for the seven new theorems in DistortionConversionCorrected.lean and Pipeline/PixelIffCorrected.lean
metadata:
  type: project
---

# Proof Plan — Tangential Conversion Physical-Semantics Fix

## Goal shapes and opening moves

### `tangential_q1_conversion_physical` / `tangential_q2_conversion_physical`

- Goal shape: equality (`q1 = p1/F`) from a universal hypothesis, div on RHS.
- Opening move: instantiate `hconsist` at the same witness points the baseline
  theorem uses (`(1,1)` for q1; `(1,0)` for q2), `simp only [mul_one, ...]` to
  clear the `*1`s.
- Expected hard step: canceling one power of F from a hypothesis of shape
  `F * p1 = q1 * F * F` down to `p1 = q1 * F`. This is genuinely a harder step
  than the baseline (which goes straight to `field_simp` + `nlinarith` on an
  `F²` hypothesis) because dividing an equation by F once, rather than
  matching an `F²` term already present, needs either `mul_left_cancel₀` after
  a `ring`-shape rewrite, or `field_simp` on the goal combined with
  `linear_combination` on the hypothesis. Plan: try `field_simp` on the goal
  first (turns `q1 = p1/F` into `q1 * F = p1`), then close with
  `linear_combination h11` (or `-h11`) — `linear_combination` handles the
  ring-rearrangement without manual `mul_left_cancel₀` bookkeeping, and is
  standard in this codebase's style (algebra classified as pure polynomial
  identity once F is cleared, so `linear_combination`/`ring`-family is the
  right tool per the algebra tripwire rules, not manual `rw` chains).
- Automation budget: `field_simp` once, `linear_combination` once. If that
  fails, fall back to `nlinarith [h11, sq_nonneg F]` after `field_simp`
  (nlinarith can sometimes close degree-2 equational goals from a linear
  hypothesis plus the nonzero-F side fact) before escalating to
  `mul_left_cancel₀`.
- Helper lemmas: none anticipated: this is a two-hypothesis, one-conclusion
  algebraic fact.

### `whole_tangential_field_iff_physical` / `_2d_iff_physical`

- Goal shape: iff, forward direction extracts two coefficients from a
  universal polynomial identity; backward direction substitutes and closes by
  `field_simp`.
- Opening move (→): specialize at `(0,1)`, `(1,0)`, `(1,1)` exactly as the
  baseline theorem does — the witness selection does not change; only the
  power of F in the resulting equations changes (F¹ terms mixed with F²
  terms instead of F² mixed with F⁴). Isolate q2 first (from `(0,1)`), then
  q1 (from `(1,1)` using q2).
- Opening move (←): `rw` the two hypotheses in, `field_simp`.
- Expected hard step: same F-cancellation issue as Layer 1, now happening
  inside a `refine ⟨?_, ?_⟩ <;> field_simp <;> nlinarith`-style block. Plan:
  attempt the same tactic combinator the baseline uses first (`field_simp <;>
  nlinarith`); if `nlinarith` cannot close a degree-mismatched goal (F¹ vs F²
  terms won't reliably fall to `nlinarith`'s bounded search), substitute
  `linear_combination` with explicit coefficients derived from the two/three
  specialized hypotheses — the same escalation path as Layer 1.
- `_2d_iff_physical`: reduces to the 1D iff via the δx component, then checks
  δy is satisfied by substitution — identical proof *shape* to
  `whole_tangential_field_2d_iff`, only the conversion formula power changes.

### `all_distortion_conversions_iff_physical`

- Goal shape: conjunction-of-foralls ↔ conjunction-of-equalities, built by
  `rw` composing three sub-iffs (two unchanged radial `whole_radial_polynomial_iff`
  calls, one new `whole_tangential_field_2d_iff_physical` call) then
  `constructor`/`rintro`/`exact` to shuffle the conjunction shape — copy the
  baseline `all_distortion_conversions_iff` proof structure verbatim, only
  substituting the physical 2D iff lemma name.
- No new algebra here; this is pure propositional shuffling once the three
  sub-iffs are available.

### `opencv_openlensio_full_pipeline_pixel_corrected`

- Goal shape: `∀ x' y', CV_pixel = OTI_pixel` (plain equality, not iff — see
  `ambiguity-register.md` AMB-TCF-001).
- Opening move: mirror `opencv_openlensio_full_pipeline_pixel_sufficiency`'s
  proof structure (it already proves exactly this equality shape, just under
  the additional `hscale : ws/w = fx` hypothesis which we no longer have and
  no longer need). Reuse its `h_num`, `h_den` radial-equality `have`s
  unchanged (they don't depend on q1/q2 at all). Replace its use of `hscale`
  to eliminate `ws` (`hws_eq : ws = w * fx`) with direct use of `hF_eq` to
  relate `(ws/w)*F` to `fx` without needing `ws = w*fx` — since we no longer
  assume `ws/w = fx`, we cannot derive `ws = w*fx`; instead derive
  `(ws/w)*F = fx` directly from `hF_eq : F = (w/ws)*fx` via `field_simp`.
- Expected hard step: the final `field_simp; ring` (or `linear_combination`)
  closing step must handle the tangential term algebra with `hq1 : q1=p1/F`,
  `hq2 : q2=p2/F` substituted, producing `F * T_cv` on the OTI side, then
  combining with `(ws/w)*F = fx` to get `fx * T_cv` — this is the one place
  where the physical fix's extra F-cancellation (same issue as Layer 1) meets
  the existing pixel-pipeline algebra. Plan: isolate this as a `have`
  (`h_tang_phys : 2*q1*(F*x')*(F*y') + q2*(...) = F*(2*p1*x'*y' + p2*(...))`)
  proved by `rw [hq1,hq2]; field_simp`, analogous to
  `PixelIffHelpers.tangential_scaled_eq` but F-scaled; then combine with a
  `have h_scale : (ws/w)*F = fx := by rw [hF_eq]; field_simp [hw,hws]` and
  finish the main goal with `field_simp` + `ring` after substituting these
  two `have`s, following the same overall structure as
  `opencv_openlensio_full_pipeline_pixel_sufficiency`'s closing block.
- Helper lemma: `tangential_scaled_eq_physical`, local to
  `Pipeline/PixelIffCorrected.lean` (not added to `PixelIffHelpers.lean` —
  keeps the new file self-contained per module-topology "clean import
  boundary" criterion; this file does not need to modify or extend the
  existing helpers file).

### `physical_pixel_agreement_scale_independent_example`

- Goal shape: existential with ~20 witnesses and a conjunction of ~12 side
  conditions plus the pixel-equality conclusion.
- Opening move: pick concrete numeric witnesses (see capsule:
  `fx=1, ws=2, w=1, F=1/2, p1=1, p2=0, k1..k6=0, cx=0`, derived `q1,q2,l*,ΔPx`
  from the conversion formulas), `refine ⟨_, _, ..., ?_⟩`, discharge numeric
  side conditions with `norm_num`, discharge the `hden` universal with
  `intro x y; norm_num` (denominator is the constant `1` when all `k4,k5,k6=0`),
  and discharge the final pixel-equality conjunct by direct application of
  `opencv_openlensio_full_pipeline_pixel_corrected` with these values.
- No new algebra; this is instantiation + one theorem application.

## Definitions to unfold

None — everything here is in terms of raw `ℝ` arithmetic expressions, no
opaque definitions to unfold (consistent with the existing `DistortionConversion.lean`
/ `Pipeline/*.lean` style, which does not use `DistortionModel.lean`'s typed
definitions at this layer).

## Theorem-discovery approach

Reuse exact witness-point choices from the four baseline theorems being
mirrored (`tangential_q1_conversion`, `tangential_q2_conversion`,
`whole_tangential_field_iff`, `whole_tangential_field_2d_iff`,
`all_distortion_conversions_iff`, `opencv_openlensio_full_pipeline_pixel_sufficiency`).
No new theorem-search needed — the only genuinely new proof-engineering
question is the single-F-cancellation step, addressed above.

## Automation budget

Per the algebra tripwires: at most two `field_simp`/`nlinarith` attempts per
goal before falling back to `linear_combination` with explicit hypothesis
coefficients; at most two manual `rw`/`ring_nf` steps before isolating into a
named `have`. If any goal requires a third distinct tactic family, emit
`ALGEBRA STOP` and record in `algebra-plan.md` before continuing.

## Slice plan (single slice — medium task)

This is proved as one slice: both new files, compiled together via
`lake env lean` on each file individually (narrowest check), then
`lake build PipelineEquivalence` and `lake build DistortionConversionCorrected`
(broader check) before Stop 4 review. No sub-slicing needed — the theorem
count (7) is small and the proof shapes are direct mirrors of existing, already
machine-checked theorems.
