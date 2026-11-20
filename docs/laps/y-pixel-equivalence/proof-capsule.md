---
name: y-pixel-equivalence-capsule
description: Proof capsule for the y-axis mirror of the full OpenCV/OpenLensIO pixel pipeline equivalence theorems (sufficiency + iff), closing PROP-003's y-pixel residual gap from the MAPS handoff
metadata:
  type: project
---

# Proof Capsule — Y-Pixel Pipeline Equivalence

## Source

MAPS → LAPS handoff: `opentrackio-proof/docs/maps/laps-handoff.md` (Property ID PROP-003, Evidence ID EVID-006).

## Intent (plain English)

`Pipeline/PixelSufficiency.lean` and `Pipeline/PixelIff.lean` prove full-pipeline pixel equivalence for the **x**-coordinate only. The project's own `docs/limitations.md` states the y-result "follows by a symmetric argument... not formally proved." This work proves the y-axis analogs:

1. `opencv_openlensio_full_pipeline_pixel_sufficiency_y` — given all parameter conversions and `h_shader/h = fy`, the OpenCV and OpenTrackIO full pipeline **y**-pixel outputs agree for all normalised input points.
2. `opencv_openlensio_full_pipeline_pixel_iff_y` — given all parameter conversions and `p1 ≠ 0 ∨ p2 ≠ 0`, y-pixel agreement holds **iff** `h_shader/h = fy`.

This closes PROP-003's y-pixel residual gap and is the discrimination-bearing check requested by the handoff (y-axis mutation-test analogs), not a restatement of the x-theorem under new names.

## The axis-swap correspondence (load-bearing fact, verified against existing project code before writing anything)

The OpenCV y-tangential term is **not** the x-term with `x'↔y'` alone — it also swaps which coefficient (`p1` vs `p2`) plays the "cross-term" role versus the "squared" role. This is already fixed by the project's own `whole_tangential_field_2d_iff` in `DistortionConversion.lean:201-213`, which states both components together:

```
δx = 2*p1*x'*y' + p2*(x'^2+y'^2+2*x'^2)
δy = p1*(x'^2+y'^2+2*y'^2) + 2*p2*x'*y'
```

So the precise substitution turning the x-theorem into the y-theorem is: `x' ↦ y'`, `y' ↦ x'`, `p1 ↦ p2`, `p2 ↦ p1`, `q1 ↦ q2`, `q2 ↦ q1`, `fx ↦ fy`, `cx ↦ cy`, `w ↦ h`, `ws (w_shader) ↦ h_shader (hs)`, `ΔPx ↦ ΔPy` — applied to the **entire** x-theorem statement and proof script. The radial numerator/denominator depend only on `x'^2+y'^2`, which is invariant under the `x'↔y'` swap, so `k1..k6`/`l1..l6` and `hl1..hl6` are **unchanged** by this substitution (they do not get swapped or renamed) — only the tangential coefficients, the two input variables, and the linear-projection parameters (`fx/cx/w/ws/ΔPx` → `fy/cy/h/h_shader/ΔPy`) move.

This matches the project's own already-proved 2D theorems: `principal_point_conversion_2d_iff` (`PrincipalPointConversion.lean:122-144`) already proves `F = (h/h_shader)*fy ∧ ΔPy = (h/h_shader)*(cy - h_shader/2)` as the y-axis half of 2D consistency, using exactly this `h, h_shader, fy, cy, ΔPy` naming — confirmed by direct inspection before this capsule was written, not assumed.

## Lean grounding

- Lean 4 `v4.29.0`, Mathlib pinned at `v4.29.0` (per `lakefile.toml`)
- New files: `opencv_opentrackio_proofs/Pipeline/PixelSufficiencyY.lean`, `Pipeline/PixelIffHelpersY.lean`, `Pipeline/PixelIffY.lean`
- New `lean_lib` entries required in `lakefile.toml` (or reuse of the existing `PixelEquivalence`/`PipelineEquivalence` globbed libs — see Theorem Location Check in the LAPS GATE)
- Imports: `DistortionConversion` (same as the x-files)

## Existing load-bearing definitions / theorems (must not change)

| Name | File | Role |
|------|------|------|
| `whole_tangential_field_2d_iff` | `DistortionConversion.lean:201` | Already states the exact y-tangential term shape this proof depends on |
| `whole_tangential_field_iff` | `DistortionConversion.lean:160` | 1D form, used inside the 2D proof |
| `principal_point_conversion_2d_iff` | `PrincipalPointConversion.lean:122` | Already proves `F=(h/h_shader)*fy`, `ΔPy=...` as part of 2D consistency — confirms y-axis naming |
| `opencv_openlensio_full_pipeline_pixel_sufficiency` | `Pipeline/PixelSufficiency.lean:30` | x-axis theorem being mirrored — statement and proof read in full before this capsule |
| `opencv_openlensio_full_pipeline_pixel_iff` | `Pipeline/PixelIff.lean:29` | x-axis theorem being mirrored |
| `radial_ratio_scaled_eq`, `tangential_scaled_eq`, `principal_offset_cancels`, `tangential_gap_forces_scale`, `pixel_eq_implies_tangential_gap` | `Pipeline/PixelIffHelpers.lean` | x-axis helper lemmas being mirrored |

## New definitions / theorems to create

| Name | File | Mirrors |
|------|------|---------|
| `opencv_openlensio_full_pipeline_pixel_sufficiency_y` | `PixelSufficiencyY.lean` | `..._sufficiency` |
| `radial_ratio_scaled_eq` (reused as-is — radial part is axis-invariant, see below) | — | — |
| `tangential_scaled_eq_y` | `PixelIffHelpersY.lean` | `tangential_scaled_eq` |
| `principal_offset_cancels_y` | `PixelIffHelpersY.lean` | `principal_offset_cancels` |
| `tangential_gap_forces_scale_y` | `PixelIffHelpersY.lean` | `tangential_gap_forces_scale` |
| `pixel_eq_implies_tangential_gap_y` | `PixelIffHelpersY.lean` | `pixel_eq_implies_tangential_gap` |
| `opencv_openlensio_full_pipeline_pixel_iff_y` | `PixelIffY.lean` | `..._iff` |

**Note on `radial_ratio_scaled_eq`:** this lemma's statement (`PixelIffHelpers.lean:13-33`) is already symmetric in its free variables `x y` — it takes `x y : ℝ` as plain arguments with no axis-specific role beyond `(F*x)` appearing linearly. Applying it with arguments swapped (`radial_ratio_scaled_eq ... F y' x'` instead of `... F x' y'`) should directly give the radius-term fact needed for the y-proof, since `x'^2+y'^2 = y'^2+x'^2`. This is a candidate for direct reuse rather than a new mirrored lemma — to be confirmed in the proof plan, not assumed here.

## Theorem texts (specification-level)

### Theorem 1 (y-sufficiency)

```lean
theorem opencv_openlensio_full_pipeline_pixel_sufficiency_y
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fy cy h_shader h F ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (h / h_shader) * fy) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hscale : h_shader / h = fy)
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    ∀ x' y' : ℝ,
      -- OpenCV pixel y-output
      fy * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * y'
           + p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') + cy
      =
      -- OpenLensIO pixel y-output (screen point (F·x', F·y'))
      (h_shader / h) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * y')
                 + q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2)
                 + 2 * q2 * (F * x') * (F * y') + ΔPy)
      + h_shader / 2
```

### Theorem 2 (y-iff)

```lean
theorem opencv_openlensio_full_pipeline_pixel_iff_y
    (... same parameter list as sufficiency, replacing hscale with hp : p1 ≠ 0 ∨ p2 ≠ 0 ...) :
    (∀ x' y' : ℝ, <same LHS = RHS as Theorem 1's conclusion>) ↔ h_shader / h = fy
```

Precise statement refined in `statement-audit.md`.

## The key mathematical fact (informal)

Mirrors `proof-plan.md`'s sibling note exactly, with axes swapped:

```
OTI pixel y-output  = fy·R_cv·y' + (h_shader/h)·δy_cv + cy
OpenCV pixel y-output = fy·R_cv·y' + fy·δy_cv + cy
```

Difference: `(h_shader/h - fy)·δy_cv`. Zero for all (x', y') iff `h_shader/h = fy` (when not all tangential terms vanish). Radial parts agree automatically after conversion — same as the x-case, since the radial factor is axis-symmetric.

## Required discrimination check (per MAPS handoff)

y-axis analogs of at least 2 of the 40 `MutationTests.lean` theorems: (a) wrong F-power for a y-side tangential coefficient (e.g. `q1 = p1/F^4` instead of `p1/F^2`) forces a degenerate condition; (b) a `p1↔p2`-coefficient-swap variant (pairing the wrong OpenCV coefficient to the wrong OTI coefficient) is shown inconsistent/degenerate. Scoped in `proof-plan.md`.

## Allowed changes

- New files `PixelSufficiencyY.lean`, `PixelIffHelpersY.lean`, `PixelIffY.lean`, and a mutation-test addition (file TBD in proof-plan.md)
- New theorems as listed above
- Local `have` statements inside proofs
- `lakefile.toml`: new lib entries if the existing `Pipeline.+` glob in the `PipelineEquivalence` lib does not already cover new `Pipeline/*.lean` files (to confirm in proof-plan.md)
- Statement refinement authorized via `statement-audit.md`

## Forbidden changes

- No changes to any existing theorem statement in any file (x-axis theorems, `whole_tangential_field_2d_iff`, `principal_point_conversion_2d_iff`, etc.)
- No changes to existing load-bearing definitions
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial` forbidden
- Do not fold in the corrected/alternative tangential formula from `DistortionConversionCorrected.lean` — use the paper's as-published `q1=p1/F^2, q2=p2/F^2` exactly, per the MAPS handoff's explicit instruction
- Do not attempt to derive `denominatorNonzero` from coefficient bounds — it stays a free hypothesis, exactly as in the x-theorem
