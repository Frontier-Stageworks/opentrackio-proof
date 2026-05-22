---
name: opencv-openlensio-pipeline-equivalence-capsule-pe04b
description: Proof capsule for SLICE-PE-04b — forward direction of opencv_openlensio_full_pipeline_pixel_iff
metadata:
  type: project
---

# Proof Capsule — PE-04b: Forward Direction of pixel_iff

## Theorem being proved (exact text from PixelIff.lean, → branch)

```lean
-- given all hypotheses of opencv_openlensio_full_pipeline_pixel_iff:
intro _h
-- Goal: ws / w = fx
-- where h : ∀ x' y', CV_pixel_x x' y' = OTI_pixel_x x' y'
```

The full theorem statement lives in `opencv_opentrackio_proofs/Pipeline/PixelIff.lean`.
The → direction receives:

```
h : ∀ x' y' : ℝ,
  fx * ((1 + k1*(x'^2+y'^2) + k2*(x'^2+y'^2)^2 + k3*(x'^2+y'^2)^3) /
        (1 + k4*(x'^2+y'^2) + k5*(x'^2+y'^2)^2 + k6*(x'^2+y'^2)^3) * x'
       + 2*p1*x'*y' + p2*(x'^2+y'^2+2*x'^2)) + cx
  =
  (ws/w) * ((1 + l1*((F*x')^2+(F*y')^2) + l3*... + l5*...) /
             (1 + l2*((F*x')^2+(F*y')^2) + l4*... + l6*...) * (F*x')
            + 2*q1*(F*x')*(F*y') + q2*((F*x')^2+(F*y')^2+2*(F*x')^2) + ΔPx)
  + ws/2

⊢ ws / w = fx
```

All coefficient conversions (hl1…hl6, hq1, hq2, hF_eq, hΔPx) are in context.
Also in context: hw, hws, hF, hF_pos, hp (p1≠0 ∨ p2≠0), hden (∀ x' y', denominator ≠ 0).

## Why the theorem matches the intended claim

After substituting all conversions, the two pixel outputs agree iff ws/w = fx.
The → direction extracts this condition from the universal equality by finding a
point where the difference is nonzero when ws/w ≠ fx.

This captures the paper's claim: coefficient conversions alone are insufficient;
ws/w = fx is the exact additional condition.

## Lean grounding

- Lean 4 v4.29.0, Mathlib v4.29.0
- File: `opencv_opentrackio_proofs/Pipeline/PixelIff.lean`
- Imports: `Pipeline.PixelSufficiency`, `Pipeline.PixelIffHelpers`
- Available helpers (in `namespace PipelineEquivalence`, from `PixelIffHelpers`):
  - `radial_ratio_scaled_eq` — OTI radial ratio at (F*x,F*y) = CV radial ratio at (x,y) * F
  - `tangential_scaled_eq` — OTI tangential at screen = CV tangential at normalised
  - `principal_offset_cancels` — (ws/w)*ΔPx + ws/2 = cx
  - `tangential_gap_forces_scale` — ∀ x y, (fx-ws/w)*T(x,y)=0 ∧ (p1≠0∨p2≠0) → ws/w=fx

## Goal shape classification

- Implication (intro h, goal is equality ws/w = fx)
- The route: h → pixel_eq_implies_tangential_gap → tangential_gap_forces_scale → ws/w=fx

## Load-bearing definitions (must not change)

| Name | File | Role |
|---|---|---|
| `opencv_openlensio_full_pipeline_pixel_iff` | PixelIff.lean | Frozen — statement not changeable |
| `tangential_gap_forces_scale` | PixelIffHelpers.lean | Key helper — already compiled |
| `radial_ratio_scaled_eq` | PixelIffHelpers.lean | Key helper — already compiled |
| `tangential_scaled_eq` | PixelIffHelpers.lean | Key helper — already compiled |
| `principal_offset_cancels` | PixelIffHelpers.lean | Key helper — already compiled |

## Allowed changes

- Add `pixel_eq_implies_tangential_gap` as a local `have` or named lemma in PixelIffHelpers.lean
- Fill the `sorry` in the → direction with a composed proof
- No other changes to PixelIff.lean or PixelIffHelpers.lean beyond the above

## Forbidden changes

- No changes to theorem statement
- No changes to hypotheses
- No `sorry`, `admit`, `axiom` in final proof
- No increasing heartbeat limits
- No expanding the full radial polynomial inside the main theorem
- No `field_simp` or `ring_nf` on the full specialized pixel equation
