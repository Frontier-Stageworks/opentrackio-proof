---
name: tangential-conversion-physical-fix-capsule
description: Proof capsule for the corrected (physical) tangential distortion conversion q1=p1/F, q2=p2/F, and its consequence for the full pixel pipeline iff
metadata:
  type: project
---

# Proof Capsule — Tangential Conversion Physical-Semantics Fix

## Intent (plain English)

`DistortionConversion.lean` faithfully formalizes the paper's stated tangential
consistency condition `δx_cv = δx_oti` (no scale factor), which yields
`q1 = p1/F²`, `q2 = p2/F²`. That theorem is **not being touched** — it correctly
documents what the paper says.

This work investigates a suspected physical error in the paper's own derivation.
The paper's coordinate-conversion equation is `ε'_x,d = F·x''` — screen-space
*distorted* coordinate equals F times the normalised *distorted* coordinate.
Expanding both sides with `ε_x = F·x'` (undistorted screen x) gives

```
ε_x + δx_oti = F·(x' + δx_cv)
F·x' + δx_oti = F·x' + F·δx_cv
δx_oti = F·δx_cv
```

i.e. the tangential displacement, being *additive*, should pick up exactly one
factor of F when converted — not zero factors (as the paper states) and not two
(which is what falls out of `q_i = p_i/F²` when re-substituted into the pixel
pipeline; see the residual-condition analysis below). The radial term needs no
such fix because it is *multiplicative*: `x'·(1+k·r²+…)`, so the F carried by
the outer `x'` already accounts for the coordinate-space change, and the
existing `l = k/F^(2n)` conversion is correct as derived.

This capsule covers a new, self-contained theorem cluster (no existing
theorems, statements, or proofs modified) proving:

1. `tangential_q1_conversion_physical`, `tangential_q2_conversion_physical` —
   Layer-1 per-term theorems under the corrected consistency hypothesis
   `F·(p_i·term) = q_i·(scaled term)`, concluding `q_i = p_i/F`.
2. `whole_tangential_field_iff_physical`, `whole_tangential_field_2d_iff_physical` —
   Layer-2 whole-polynomial iff theorems, corrected scaling.
3. `all_distortion_conversions_iff_physical` — full 8-parameter iff, radial part
   unchanged (F^(2n) scaling, no bug there), tangential part corrected.
4. `opencv_openlensio_full_pipeline_pixel_corrected` — the pixel-level
   consequence: under the corrected `hq1 : q1 = p1/F`, `hq2 : q2 = p2/F` (all
   other hypotheses as in `opencv_openlensio_full_pipeline_pixel_iff`), full
   pixel-x agreement holds **unconditionally** for all `x', y'` — no
   `ws/w = fx` side condition, no `p1 ≠ 0 ∨ p2 ≠ 0` hypothesis.
5. `physical_pixel_agreement_scale_independent_example` — a concrete numeric
   witness (existential) with `ws/w ≠ fx` where pixel agreement still holds
   under the corrected conversions, mechanically refuting the naive analog of
   the existing iff (`pixel_eq ↔ ws/w = fx`) under the physical hypotheses.

## Why this predicts the residual condition collapses

Substituting `q1 = p1/F`, `q2 = p2/F` into the OTI tangential term:

```
2·q1·(Fx')·(Fy') + q2·((Fx')² + (Fy')² + 2(Fx')²)
= 2·(p1/F)·F²·x'·y' + (p2/F)·F²·(x'²+y'²+2x'²)
= F·(2·p1·x'·y' + p2·(x'²+y'²+2x'²))
= F · T_cv(x', y')
```

This is exactly the same F-scaling the radial term already carries through
`R_oti(F·x', F·y')·(F·x') = F · R_cv(x', y') · x'` (proved unconditionally by
the existing, unmodified `radial_ratio_scaled_eq` — it does not depend on
q1/q2 at all). So:

```
OTI inner = F·R_cv·x' + F·T_cv + ΔPx = F·(R_cv·x' + T_cv) + ΔPx
OTI pixel = (ws/w)·OTI inner + ws/2
          = (ws/w)·F·(R_cv·x' + T_cv) + (ws/w)·ΔPx + ws/2
          = fx·(R_cv·x' + T_cv) + cx        [(ws/w)·F = fx via hF_eq; principal offset cancels]
CV pixel  = fx·(R_cv·x' + T_cv) + cx         [definition]
```

Both sides are syntactically the same expression — no `ws/w = fx` needed. This
is the predicted "collapses to trivially true" outcome; the theorem below
confirms it mechanically.

## Lean grounding

- Lean 4 `v4.29.0`, Mathlib `v4.29.0` (unchanged toolchain)
- New file 1: `opencv_opentrackio_proofs/DistortionConversionCorrected.lean`
  (top-level, sibling of `DistortionConversion.lean`) — needs a new
  `[[lean_lib]]` entry in `lakefile.toml` (default glob = self-named module,
  matching the existing per-file lib pattern for this directory).
- New file 2: `opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean`
  (sibling of `Pipeline/PixelIff.lean`) — automatically covered by the
  existing `PipelineEquivalence` lib's `globs = ["PipelineEquivalence",
  "Pipeline.+"]`; no lakefile change needed for this file.

## Existing load-bearing definitions/theorems used, NOT modified

| Name | File | Role |
|------|------|------|
| `radial_ratio_scaled_eq` | `Pipeline/PixelIffHelpers.lean` (`PipelineEquivalence` namespace) | Radial part of pixel pipeline agrees unconditionally after `l_i = k_i/F^(2n)`; reused as-is, no q1/q2 dependency |
| `principal_offset_cancels` | `Pipeline/PixelIffHelpers.lean` | `(ws/w)·ΔPx + ws/2 = cx`; reused as-is |
| `whole_radial_polynomial_iff` | `DistortionConversion.lean` | Radial iff, unchanged — reused in `all_distortion_conversions_iff_physical` |

All existing theorems in `DistortionConversion.lean`, `PixelIffHelpers.lean`,
`PixelSufficiency.lean`, `PixelIff.lean` are read-only in this task.

## New theorem texts (specification-level)

```lean
-- DistortionConversionCorrected.lean

theorem tangential_q1_conversion_physical
    (p1 q1 F : ℝ) (hF : F ≠ 0)
    (hconsist : ∀ x' y' : ℝ, F * (p1 * x' * y') = q1 * (F * x') * (F * y')) :
    q1 = p1 / F

theorem tangential_q2_conversion_physical
    (p2 q2 F : ℝ) (hF : F ≠ 0)
    (hconsist : ∀ r x' : ℝ, F * (p2 * (r ^ 2 + 2 * x' ^ 2)) = q2 * ((F * r) ^ 2 + 2 * (F * x') ^ 2)) :
    q2 = p2 / F

theorem whole_tangential_field_iff_physical
    (p1 p2 q1 q2 F : ℝ) (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        F * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2)) ↔
    q1 = p1 / F ∧ q2 = p2 / F

theorem whole_tangential_field_2d_iff_physical
    (p1 p2 q1 q2 F : ℝ) (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        F * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) =
          2 * q1 * (F * x') * (F * y') +
            q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) ∧
        F * (p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') =
          q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
            2 * q2 * (F * x') * (F * y')) ↔
    q1 = p1 / F ∧ q2 = p2 / F

theorem all_distortion_conversions_iff_physical
    (k1 k2 k3 k4 k5 k6 : ℝ) (l1 l2 l3 l4 l5 l6 : ℝ) (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ r : ℝ, <radial numerator eq, unchanged shape>) ∧
    (∀ r : ℝ, <radial denominator eq, unchanged shape>) ∧
    (∀ x' y' : ℝ, <physical tangential δx ∧ δy, F-scaled as above>) ↔
    l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6 ∧
    l2 = k4 / F ^ 2 ∧ l4 = k5 / F ^ 4 ∧ l6 = k6 / F ^ 6 ∧
    q1 = p1 / F ∧ q2 = p2 / F
```

```lean
-- Pipeline/PixelIffCorrected.lean

theorem opencv_openlensio_full_pipeline_pixel_corrected
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F) (hq2 : q2 = p2 / F)                         -- CORRECTED
    (hF_eq : F = (w / ws) * fx) (hΔPx : ΔPx = (w / ws) * (cx - ws / 2))
    (hden : ∀ x' y' : ℝ, <radial denominator ≠ 0, unchanged>) :
    ∀ x' y' : ℝ, <CV pixel-x> = <OTI pixel-x>
    -- NOTE: no `hscale : ws/w = fx`, no `hp : p1 ≠ 0 ∨ p2 ≠ 0` — see residual-condition analysis

theorem physical_pixel_agreement_scale_independent_example :
    ∃ k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
      fx cx ws w F ΔPx : ℝ,
      <all hypotheses of the theorem above hold> ∧
      ws / w ≠ fx ∧
      (∀ x' y' : ℝ, <CV pixel-x> = <OTI pixel-x>)
```

## Allowed changes

- Two new files as listed above.
- One new `[[lean_lib]]` entry in `lakefile.toml` for `DistortionConversionCorrected`.
- README updates in `opencv_opentrackio_proofs/README.md`,
  `opencv_opentrackio_proofs/Pipeline/README.md`, and `docs/limitations.md`
  to note this is an investigation of a suspected paper-level error, distinct
  from the as-published formalization.
- Local `have`/helper lemmas inside the two new files.
- Statement refinement of the theorem texts above during Stop 3, if the exact
  Lean shape needs adjustment for provability — must be recorded in
  `statement-audit.md`/`ambiguity-register.md` before proceeding, not silently
  changed.

## Forbidden changes

- No edits to `DistortionConversion.lean`, `PixelIffHelpers.lean`,
  `PixelSufficiency.lean`, `PixelIff.lean`, or any other existing theorem or
  definition.
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial` forbidden.
- No silent reshaping of the `opencv_openlensio_full_pipeline_pixel_corrected`
  conclusion away from unconditional pixel agreement — if the algebra does
  not in fact collapse to trivially-true (contradicting the hand analysis
  above), STOP and record in `ambiguity-register.md` rather than forcing a
  different statement to compile.
