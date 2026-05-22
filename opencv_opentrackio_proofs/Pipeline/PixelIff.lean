/-
  Pipeline/PixelIff.lean

  Conditional iff: given all parameter conversions, full pixel x-output agreement
  for every normalised input ↔ ws/w = fx.

  Both directions proved. The → direction composes pixel_eq_implies_tangential_gap
  and tangential_gap_forces_scale from PixelIffHelpers.
-/

import Pipeline.PixelSufficiency
import Pipeline.PixelIffHelpers

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_iff  (conditional iff)

  Given all parameter conversions hold (l_i = k_i/F^(2n), q_i = p_i/F^2,
  F = (w/ws)*fx, ΔPx = (w/ws)*(cx - ws/2)), the full pixel x-outputs agree
  for every normalised input point if and only if ws/w = fx.

  This is the paper's central claim: the coefficient conversions alone are not
  sufficient; the scale ratio ws/w = fx is exactly the additional condition
  that bridges the gap between the two pipelines.

  Requires hp : p1 ≠ 0 ∨ p2 ≠ 0 for the → direction (to find a point where the
  tangential term δx_cv is nonzero, so we can cancel and conclude ws/w = fx).
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_iff
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (w / ws) * fx) (hΔPx : ΔPx = (w / ws) * (cx - ws / 2))
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    (∀ x' y' : ℝ,
      fx * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * x'
           + 2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) + cx
      =
      (ws / w) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * x')
                 + 2 * q1 * (F * x') * (F * y')
                 + q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) + ΔPx)
      + ws / 2)
    ↔ ws / w = fx := by
  constructor
  · -- → direction: universal pixel equality → ws/w = fx
    intro h
    exact PipelineEquivalence.tangential_gap_forces_scale p1 p2 fx ws w hw hws hp
      (PipelineEquivalence.pixel_eq_implies_tangential_gap
        k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
        fx cx ws w F ΔPx
        hw hws hF hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2 hF_eq hΔPx hden h)
  · -- ← direction: ws/w = fx implies pixel agreement for all (x', y')
    intro hscale
    exact opencv_openlensio_full_pipeline_pixel_sufficiency
        k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
        fx cx ws w F ΔPx
        hw hws hF hF_pos hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2
        hF_eq hΔPx hscale hden
