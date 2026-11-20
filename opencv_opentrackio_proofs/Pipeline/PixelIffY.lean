/-
  Pipeline/PixelIffY.lean

  Y-axis mirror of Pipeline/PixelIff.lean. Conditional iff: given all parameter
  conversions, full pixel y-output agreement for every normalised input ↔
  h_shader/h = fy.

  Both directions proved. The → direction composes
  pixel_eq_implies_tangential_gap_y and tangential_gap_forces_scale_y from
  PixelIffHelpersY.
-/

import Pipeline.PixelSufficiencyY
import Pipeline.PixelIffHelpersY

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_iff_y  (conditional iff)

  Given all parameter conversions hold (l_i = k_i/F^(2n), q_i = p_i/F^2,
  F = (h/h_shader)*fy, ΔPy = (h/h_shader)*(cy - h_shader/2)), the full pixel
  y-outputs agree for every normalised input point if and only if
  h_shader/h = fy.

  Y-axis analog of opencv_openlensio_full_pipeline_pixel_iff — see
  docs/laps/y-pixel-equivalence/ for the derivation confirming the axis-swap
  correspondence (this is NOT merely the x-theorem with x'/y' textually
  swapped; the tangential coefficient roles (p1 vs p2) also swap, per
  whole_tangential_field_2d_iff's δy component).

  Requires hp : p1 ≠ 0 ∨ p2 ≠ 0 for the → direction (to find a point where the
  tangential term δy_cv is nonzero, so we can cancel and conclude
  h_shader/h = fy).
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_iff_y
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fy cy h_shader h F ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (h / h_shader) * fy) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    (∀ x' y' : ℝ,
      fy * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * y'
           + p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') + cy
      =
      (h_shader / h) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * y')
                 + q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2)
                 + 2 * q2 * (F * x') * (F * y') + ΔPy)
      + h_shader / 2)
    ↔ h_shader / h = fy := by
  constructor
  · -- → direction: universal pixel equality → h_shader/h = fy
    intro hpx
    exact PipelineEquivalence.tangential_gap_forces_scale_y p1 p2 fy h_shader h hh hhs hp
      (PipelineEquivalence.pixel_eq_implies_tangential_gap_y
        k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
        fy cy h_shader h F ΔPy
        hh hhs hF hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2 hF_eq hΔPy hden hpx)
  · -- ← direction: h_shader/h = fy implies pixel agreement for all (x', y')
    intro hscale
    exact opencv_openlensio_full_pipeline_pixel_sufficiency_y
        k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
        fy cy h_shader h F ΔPy
        hh hhs hF hF_pos hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2
        hF_eq hΔPy hscale hden
