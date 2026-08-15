---
name: tangential-conversion-physical-fix-statement-audit
description: Audit of whether the corrected theorem statements capture the intended physical-consistency claim, and why the existing paper-faithful theorems are the right baseline to diff against
metadata:
  type: project
---

# Statement Audit — Tangential Conversion Physical-Semantics Fix

## Baseline being diffed against (unchanged, read-only)

`tangential_q1_conversion` (`DistortionConversion.lean:71-80`):
hypothesis `∀ x' y', p1 * x' * y' = q1 * (F*x') * (F*y')`, concludes `q1 = p1/F²`.
This correctly formalizes the paper's literal stated equation `δx_cv = δx_oti`
(no coordinate-space scale factor on either side). It is **not wrong as a
formalization of the paper** — it is being kept exactly as-is to document what
the paper says.

## Intended physical claim (plain English)

The paper's own coordinate map for the *distorted* point is `ε'_x,d = F · x''`
(Eq. in the source paper relating OTI screen-space distorted coordinate to
OpenCV normalised-space distorted coordinate). Both `x''` (OpenCV) and `ε'_x,d`
(OTI) are the *undistorted coordinate plus the distortion displacement*:

```
x''    = x'   + δx_cv(x', y')
ε'_x,d = ε_x  + δx_oti(ε_x, ε_y),   ε_x = F·x', ε_y = F·y'
```

Substituting into `ε'_x,d = F·x''`:

```
F·x' + δx_oti(F·x', F·y') = F·(x' + δx_cv(x', y'))
                           = F·x' + F·δx_cv(x', y')
⟹ δx_oti(F·x', F·y') = F·δx_cv(x', y')
```

This is the intended hypothesis: **`F` times the CV displacement equals the OTI
displacement**, not equality without the F factor. The corrected theorems below
formalize exactly this.

## Corrected statement, per theorem

### `tangential_q1_conversion_physical`

- Hypothesis: `∀ x' y' : ℝ, F * (p1 * x' * y') = q1 * (F * x') * (F * y')`.
  This is `F * δx_cv|cross-term = δx_oti|cross-term`, i.e. exactly `F·δx_cv = δx_oti`
  restricted to the cross term.
- Conclusion: `q1 = p1 / F`.
- Semantic match: the hypothesis is the F-scaled analog of the existing
  `tangential_q1_conversion` hypothesis (identical except for the `F *` on the
  left), and the conclusion drops one power of F accordingly. This is a direct,
  minimal, one-parameter-family diff — not a different theorem shape.
- Non-vacuity: `hconsist` is instantiated at a nonzero witness `(1,1)`, exactly
  as the baseline theorem does; no risk of vacuous forall.

### `tangential_q2_conversion_physical`

- Same structure, `F *` inserted on the CV side of the radial-shaped tangential
  term. Conclusion `q2 = p2/F`. Mirrors `tangential_q2_conversion`.

### `whole_tangential_field_iff_physical` / `_2d_iff_physical`

- Same iff shape as the baseline `whole_tangential_field_iff` /
  `whole_tangential_field_2d_iff`, with `F *` inserted on the CV (left) side of
  each equation and `q_i = p_i/F` (not `/F²`) in the conclusion.
- The ← direction substitutes `q1 = p1/F, q2 = p2/F` into the RHS and must
  reduce, via `field_simp`, to `F * (CV term) = F * (CV term)` — algebraically
  guaranteed since `q_i * F² = p_i * F` when `q_i = p_i/F`. No new proof
  obligation shape versus the baseline; only the power of F changes.

### `all_distortion_conversions_iff_physical`

- Radial conjuncts: **unchanged** from `all_distortion_conversions_iff` — the
  radial part of the paper's derivation is not being disputed (see capsule:
  the multiplicative radial term already carries its own F through the outer
  `x'` factor, so `l_i = k_i/F^(2n)` is correct as derived and requires no fix).
- Tangential conjunct: replaced with the physical (F-scaled) version.
- This produces a theorem whose radial half is literally identical in
  statement to the existing one and whose tangential half is the corrected
  version — a faithful "only the buggy part changes" diff.

### `opencv_openlensio_full_pipeline_pixel_corrected`

- Same hypothesis list as `opencv_openlensio_full_pipeline_pixel_iff` **except**:
  - `hq1 : q1 = p1 / F` (was `/ F ^ 2`)
  - `hq2 : q2 = p2 / F` (was `/ F ^ 2`)
  - `hp : p1 ≠ 0 ∨ p2 ≠ 0` — **dropped**. This hypothesis existed solely to
    support the → direction's extraction of `ws/w = fx` from a nonvanishing
    tangential gap. Under the corrected conversion, the hand-derivation in the
    proof capsule shows the "gap" `(fx - ws/w)·T_cv` term vanishes identically
    (not merely at witness points) *regardless of T_cv*, so there is no
    → direction to prove and no need to rule out `T_cv ≡ 0`.
  - `hscale : ws / w = fx` — **dropped from hypotheses entirely**; the
    conclusion no longer needs it as a precondition because it is no longer a
    precondition of the algebra at all (see below).
- Conclusion: changed from an `↔` (`pixel_eq ↔ ws/w = fx`) to a plain
  `∀ x' y', pixel_eq` — an unconditional universal statement, not a
  biconditional. **This is a deliberate, load-bearing statement-shape change**,
  authorized here because it is not a weakening for convenience — it is the
  mathematically correct statement once the bug is fixed. Keeping the `↔`
  shape and trying to prove `pixel_eq ↔ ws/w = fx` under the corrected
  hypotheses would be **provably false** in general (see
  `physical_pixel_agreement_scale_independent_example`, which exhibits
  `ws/w ≠ fx` with `pixel_eq` still holding) — attempting to force that iff to
  compile would require either a false theorem or a hidden hypothesis that
  secretly re-imposes `ws/w = fx`, which would defeat the purpose of the
  investigation. Recorded in `ambiguity-register.md` AMB-TCF-001.

### `physical_pixel_agreement_scale_independent_example`

- Purely existential witness theorem; exists specifically to make the "the
  naive iff would be false" claim machine-checked rather than prose-only. Not
  a general theorem — a concrete counterexample instance discharged by
  `norm_num`/`refine` plus one application of
  `opencv_openlensio_full_pipeline_pixel_corrected`.

## Vacuity check

None of the five `DistortionConversionCorrected.lean` theorems have hypotheses
that force their own conclusion trivially (e.g. no hypothesis of shape
`q1 = p1/F` appears anywhere in the antecedents). `hF : F ≠ 0` is necessary
(division) and appears in the baseline theorems too — not a new vacuity risk.

`opencv_openlensio_full_pipeline_pixel_corrected` has one fewer hypothesis than
the baseline iff theorem (`hp`, `hscale` both dropped) and a *stronger*
unconditional conclusion (plain equality holding for all `x', y'`, vs. an iff
whose one direction required extra work) — this is a strengthening, not a
weakening, and is exactly the expected shape once the bug is fixed: the extra
condition disappears because it was an artifact of the bug, not a genuine
physical requirement.
